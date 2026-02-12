#include "internal.hpp"
#include <cstddef>
#include <cstdint>
#include <limits>
#include <vector>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Random walk local search based on yallin ideas, as simplified by our master
// students Johannes Gröber and Jakob Peterson and Andris Rico, but adapted to
// the full occurrence list that we need in CaDiCaL.
//
// The implementation requires to give clauses a weight and store various
// information. We put those into a separate vector und rely on the indices
// instead, similir to the version of walk with full occurrences.
//
// One difference to the original implementation is that we do not do restarts
// and instead rely on CDCL to do that for us. Another difference is that we
// cannot flip assumption literals, which are all set on level 1.
//
// Compared to `walk.cpp`, we do not optimize for binary clauses. At
// least not yet, but it is not clear how to keep the weights.
//
// Compared to `walk_full_occs` which is the Kissat version, we use
// `size_t` instead of unsigned because the only gain is the size of
// the occurrences, but not in the information of the clauses.
//
// For ticks, we assume that the main array containing all clauses is
// always in cache.
struct DDFW_Tagged {
  size_t counter_pos;
#ifndef NDEBUG
  Clause *c;
#endif
  explicit DDFW_Tagged () { assert (false); }
  explicit DDFW_Tagged (Clause *d, size_t pos)
      : counter_pos (pos) {
#ifndef NDEBUG
    c = d;
#else
    (void) d;
#endif
  }
};

// This is the main structure containing all informations about any
// clause: its weight, the critical variable (if any), the number of
// true literals, and the position in the array of broken clauses.
struct DDFW_Counter {
  Clause *clause; // pointer to the clause itself
  double weight;
  unsigned critical; // critical literal if any
  unsigned count; // number of true literals
  size_t pos;   // pos in the broken clauses
  explicit DDFW_Counter (unsigned c, size_t p, unsigned crit, Clause *d, double w)
      : clause (d), weight (w), critical (crit), count (c), pos (p){}
  explicit DDFW_Counter (unsigned c, size_t p, Clause *d, double w)
      : clause (d), weight (w), critical (0), count (c), pos (p){}
  explicit DDFW_Counter (unsigned c, Clause *d, double w)
      :  clause (d), weight (w), critical (0), count (c), pos (UINT32_MAX) {}
  explicit DDFW_Counter (unsigned c, Clause *d, double w, unsigned xor_lits)
      :  clause (d), weight (w), critical (xor_lits), count (c), pos (UINT32_MAX) {}
  DDFW_Counter () = default;
  DDFW_Counter (const DDFW_Counter& d) = default;
  DDFW_Counter (DDFW_Counter&& d) = default;
  ~DDFW_Counter () = default;
  DDFW_Counter &operator= (const DDFW_Counter &) = default;
};

struct Walker_DDFW {
  static constexpr size_t invalid_position = UINT32_MAX;
  Internal *internal;

  // for efficiency, storing the model each time an improvement is
  // found is too costly. Instead we store some of the flips since
  // last time and the position of the best model found so far.
  Random random;         // local random number generator
  int64_t ticks;         // ticks to approximate run time
  int64_t limit;         // limit on number of propagations
  vector<DDFW_Tagged> broken; // currently unsatisfied clauses
  std::vector<double> var_critical_sat_weights;
  std::vector<double> var_unsat_weights;
  std::vector<int>  flips; // remember the flips compared to the last best saved model
  int best_trail_pos;
  size_t minimum = (size_t)-1;
  std::vector<signed char> best_values; // best model found so far


  // variables appearing in a broken clause, called uvars in the paper
  std::vector<int> vars_in_broken;
  std::vector<size_t> position_vars_in_broken;
  std::vector<size_t> noccs_vars_in_broken;
  size_t last_searched_vars_in_broken;

  // for sideways jumps, we remember all the literals that have no impact on the overall cost
  std::vector<int> no_gain_literals;

  // the core part: the weights
  std::vector<DDFW_Counter> weight_clause_info;
  // walk occurrences
  std::vector<std::vector<DDFW_Tagged>> woccs;


  static constexpr double w_0 = 8.0;

  using TOccs = std::vector<DDFW_Tagged>;
  TOccs &occs (int lit) {
    const int idx = internal->vlit (lit);
    assert ((size_t) idx < woccs.size ());
    return woccs[idx];
  }
  const TOccs &occs (int lit) const {
    const int idx = internal->vlit (lit);
    assert ((size_t) idx < woccs.size ());
    return woccs[idx];
  }
  const double &critical_sat_weight (int lit) const {
    assert ((size_t)internal->vidx (lit) < var_critical_sat_weights.size());
    return var_critical_sat_weights[internal->vidx (lit)];
  }
  double &critical_sat_weight (int lit) {
    assert ((size_t)internal->vidx (lit) < var_critical_sat_weights.size());
    return var_critical_sat_weights[internal->vidx (lit)];
  }
  const double &critical_unsat_weight (int lit) const {
    assert ((size_t)internal->vidx (lit) < var_unsat_weights.size());
    return var_unsat_weights[internal->vidx (lit)];
  }
  double &critical_unsat_weight (int lit) {
    assert ((size_t)internal->vidx (lit) < var_unsat_weights.size());
    return var_unsat_weights[internal->vidx (lit)];
  }
  const size_t &uvar_count (int lit) const {
    assert ((size_t)internal->vidx (lit) < noccs_vars_in_broken.size());
    return noccs_vars_in_broken[internal->vidx (lit)];
  }
  size_t &uvar_count (int lit) {
    assert ((size_t)internal->vidx (lit) < noccs_vars_in_broken.size());
    return noccs_vars_in_broken[internal->vidx (lit)];
  }

  DDFW_Counter &clause_info (size_t pos) {
    assert (pos < weight_clause_info.size ());
    return weight_clause_info[pos];
  }

  const DDFW_Counter &clause_info (size_t pos) const {
    assert (pos < weight_clause_info.size ());
    return weight_clause_info[pos];
  }
  void connect_clause (int lit, Clause *clause, size_t pos) {
    assert (pos < weight_clause_info.size ());
    assert (clause_info(pos).clause == clause);
    LOG (clause, "connecting clause on %d with already in occurrences %zu",
         lit, occs (lit).size ());
    occs (lit).push_back (DDFW_Tagged (clause, pos));
  }
  void connect_clause (Clause *clause, size_t pos) {
    assert (pos < weight_clause_info.size ());
    assert (clause_info (pos).clause == clause);
    for (auto lit : *clause)
      connect_clause (lit, clause, pos);
  }

  void add_uvar (int lit) {
    const int idx = internal->vidx (lit);
    if (internal->var (lit).level == 1) {
      LOG ("cannot mark %s as uvar", LOGLIT (lit));
      return;
    }
    if (!noccs_vars_in_broken[idx]) {
      position_vars_in_broken[idx] = vars_in_broken.size ();
      vars_in_broken.push_back(idx);
    }
    ++noccs_vars_in_broken[idx];
    LOG ("marking %s as uvar, found %zd times", LOGLIT (lit), noccs_vars_in_broken[idx]);
  }
  void remove_uvar (int lit) {
    if (internal->var (lit).level == 1)
      return;
    assert (uvar_count (lit) >= 1);
    if (uvar_count (lit) == 1) {
      size_t pos = position_vars_in_broken[internal->vidx (lit)];
      assert (pos < vars_in_broken.size ());
      vars_in_broken[pos] = vars_in_broken.back ();
      int old_idx = vars_in_broken[pos];
      vars_in_broken.pop_back();
      position_vars_in_broken[old_idx] = pos;
    }
    --uvar_count (lit);
    LOG ("unmarking %s as uvar once, remaining %zd times", LOGLIT (lit), noccs_vars_in_broken[internal->vidx (lit)]);
  }

  // Finds the variable that only reduces the most number of unsatisfied
  // clauses.
  std::pair<int,double> find_weight_reducing_variable ();

  // Finds and flips one literals which does not reduce the number of
  // unsatisfied clauses (but does not make it worse either)
  void do_sideways_jump ();
  // Transfer the weights from the satisfied to the unsatisfied clauses to
  // increase the focuse on the latter, the hard-to-satisfy clauses
  void transfer_weights ();
  size_t maximum_weight_neighbor (Clause *c);
  size_t random_satisfied_big_weight_clause (double w_0);
  void update_unsat_weights (size_t pos, double);
  void update_sat_weights (size_t pos, double);


  void check_occs () const {
#ifndef NDEBUG
    std::vector<double> sat_weights;
    std::vector<double> unsat_weights;
    sat_weights.resize(internal->max_var+1, 0);
    unsat_weights.resize(internal->max_var+1, 0);
    for (auto lit : internal->lits) {
      for (auto w : occs (lit)) {
        assert (w.counter_pos < weight_clause_info.size ());
      }
    }

    unsigned unsatisfied = 0;
    for (auto c : weight_clause_info) {
      unsigned count = 0;
      LOG (c.clause, "checking clause with counter %d at position %zd and weight %f:", c.count, c.pos, c.weight);
      unsigned xor_lit = 0;
      bool satisfied = 0;
      for (auto lit : *c.clause) {
        if (internal->val (lit) > 0) {
          ++count;
          xor_lit ^= internal->vidx (lit);
          satisfied = true;
        }
      }
      assert (count == c.count);
      assert (c.critical == xor_lit);
      if (!count)
        ++unsatisfied;
      if (!satisfied) {
        assert (c.pos < broken.size ());
        assert (broken[c.pos].c == c.clause);
      }
      if (count == 1) {
        sat_weights[internal->vidx (xor_lit)] += c.weight;
      }
      if (!count){
        for (auto lit : *c.clause) {
          unsat_weights[internal->vidx (lit)] += c.weight;
        }
      }
    }
    assert (broken.size () == unsatisfied);

    for (auto v : internal->vars) {
      // exact values do not work due to rounding issues. The values
      // 0.001 might be too small already, but mobical seems to go
      // through.
      assert (std::abs (unsat_weights[internal->vidx (v)] - critical_unsat_weight(v)) < 0.001);
      assert (std::abs (sat_weights[internal->vidx (v)] - critical_sat_weight(v)) < 0.001);
    }
#endif
  }

  void check_vars_in_broken () const {
#ifndef NDEBUG
  std::vector<size_t> count(internal->max_var + 1, 0);
    for (size_t i = 0; i < broken.size (); ++i) {
      const DDFW_Tagged t = broken[i];
      assert (t.c);
      assert (t.counter_pos < weight_clause_info.size ());
      assert (clause_info (t.counter_pos).clause == t.c);
      for (auto lit : *t.c) {
        assert (internal->val (lit) < 0);
        ++count[internal->vidx (lit)];
      }
    }
  for (auto v : internal->vars) {
    // for assumption, count is not important:
    if (internal->var (v).level == 1)
      continue;
    assert (count[v] == uvar_count (v));
    if (count[v]) {
      assert (position_vars_in_broken[v] < vars_in_broken.size ());
      assert (vars_in_broken[position_vars_in_broken[v]] == v);
    }
  }
#endif
  }

  void check_broken () const {
#ifndef NDEBUG
    for (size_t i = 0; i < broken.size (); ++i) {
      const DDFW_Tagged t = broken[i];
      assert (t.c);
      assert (t.counter_pos < weight_clause_info.size ());
      assert (clause_info (t.counter_pos).clause == t.c);
      for (auto lit : *t.c) {
        assert (internal->val (lit) < 0);
      }
    }
#endif
  }

  void check_all () const {
    check_broken ();
    check_occs ();
    check_vars_in_broken();
  }

  void make_clause (DDFW_Tagged t, int);

  Walker_DDFW (Internal *, int64_t limit);
  void push_flipped (int flipped);
  void save_walker_trail (bool);
  void save_final_minimum (size_t old_minimum);
  void make_clauses_along_occurrences (int lit);
  void make_clauses_along_unsatisfied (int lit);
  void make_clauses (int lit);
  void break_clauses (int lit);
  unsigned walk_ddfw_pick_clause ();
  void walk_ddfw_flip_lit (int lit);
  int walk_ddfw_pick_lit (Clause *);
  unsigned walk_ddfw_break_value (int lit);
};

// Initialize the data structures for one local search round.

Walker_DDFW::Walker_DDFW (Internal *i, int64_t l)
    : internal (i), random (internal->opts.seed), // global random seed
      ticks (0), limit (l), best_trail_pos (-1) {
  random += internal->stats.walk.count; // different seed every time
  flips.reserve (i->max_var / 4);
  best_values.resize (i->max_var + 1, 0);
  woccs.resize (i->max_var * 2 + 2);
  weight_clause_info.reserve (1+internal->irredundant());
}

// Add the literal to flip to the queue

void Walker_DDFW::push_flipped (int flipped) {
  LOG ("push literal %s on the flips", LOGLIT (flipped));
  assert (flipped);
  if (best_trail_pos < 0) {
    LOG ("not pushing flipped %s to already invalid trail",
         LOGLIT (flipped));
    return;
  }

  const size_t size_trail = flips.size ();
  const size_t limit = internal->max_var / 4 + 1;
  if (size_trail < limit) {
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zd",
         LOGLIT (flipped), size_trail + 1);
    return;
  }

  if (best_trail_pos) {
    LOG ("trail reached limit %zd but has best position %d", limit,
         best_trail_pos);
    save_walker_trail (true);
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zu",
         LOGLIT (flipped), flips.size ());
    return;
  } else {
    LOG ("trail reached limit %zd without best position", limit);
    flips.clear ();
    LOG ("not pushing %s to invalidated trail", LOGLIT (flipped));
    best_trail_pos = -1;
    LOG ("best trail position becomes invalid");
  }
}

void Walker_DDFW::save_walker_trail (bool keep) {
  assert (best_trail_pos != -1);
  assert ((size_t) best_trail_pos <= flips.size ());
#ifdef LOGGING
  const size_t size_trail = flips.size ();
#endif
  const int kept = flips.size () - best_trail_pos;
  LOG ("saving %d values of flipped literals on trail of size %zd",
       best_trail_pos, size_trail);

  const auto begin = flips.begin ();
  const auto best = flips.begin () + best_trail_pos;
  const auto end = flips.end ();

  auto it = begin;
  for (; it != best; ++it) {
    const int lit = *it;
    assert (lit);
    const signed char value = sign (lit);
    const int idx = std::abs (lit);
    best_values[idx] = value;
  }
  if (!keep) {
    LOG ("no need to shift and keep remaining %u literals", kept);
    return;
  }

#ifndef NDEBUG
  for (auto v : internal->vars) {
    if (internal->active (v))
      assert (best_values[v] == internal->phases.saved[v]);
  }
#endif
  LOG ("flushed %u literals %.0f%% from trail", best_trail_pos,
       percent (best_trail_pos, size_trail));
  assert (it == best);
  auto jt = begin;
  for (; it != end; ++it, ++jt) {
    assert (jt <= it);
    assert (it < end);
    *jt = *it;
  }

  assert ((int) (end - jt) == best_trail_pos);
  assert ((int) (jt - begin) == kept);
  flips.resize (kept);
  LOG ("keeping %u literals %.0f%% on trail", kept,
       percent (kept, size_trail));
  LOG ("reset best trail position to 0");
  best_trail_pos = 0;
}

// finally export the final minimum
void Walker_DDFW::save_final_minimum (size_t old_init_minimum) {
  assert (minimum <= old_init_minimum);
#ifdef NDEBUG
  (void) old_init_minimum;
#endif

  if (!best_trail_pos || best_trail_pos == -1)
    LOG ("minimum already saved");
  else
    save_walker_trail (false);

  ++internal->stats.walk.improved;
  for (auto v : internal->vars) {
    if (best_values[v])
      internal->phases.saved[v] = best_values[v];
    else
      assert (!internal->active (v));
  }
  internal->copy_phases (internal->phases.prev);
}

/*------------------------------------------------------------------------*/
void Walker_DDFW::make_clause (DDFW_Tagged t, int lit) {
  assert (internal->val (lit) > 0);
  assert (t.counter_pos < weight_clause_info.size ());
  DDFW_Counter &d = clause_info (t.counter_pos);
  const unsigned old_critical = d.critical;
  d.critical ^= internal->vidx (lit);
  auto old_count = d.count++;
  if (old_count) {
    LOG (d.clause,
         "already made with counter %d at position %zd",
         d.count, d.pos);
    assert (d.clause == t.c);
    assert (d.pos == invalid_position);
    if (old_count == 1) {
      critical_sat_weight (old_critical) -= d.weight;
    }
    return;
  }
  LOG (d.clause,
       "make with counter %d at position %zd", d.count,
       d.pos);
  assert (d.pos != invalid_position);
  assert (d.pos < broken.size ());
  ++ticks;
  auto last = broken.back ();
#ifndef NDEBUG
  assert (clause_info (t.counter_pos).clause == t.c);
  assert (last.counter_pos < weight_clause_info.size ());
  assert (clause_info (last.counter_pos).clause == last.c);
#endif
  size_t pos = d.pos;
  assert (pos < broken.size ());
  broken[pos] = last;
  // the order is important
  clause_info(last.counter_pos).pos = pos;
  d.pos = invalid_position;
  broken.pop_back ();

  ++ticks;
  for (auto l : *d.clause) {
    int idx = internal->vidx (l);
    remove_uvar(idx);
    critical_unsat_weight (l) -= d.weight;
  }
  LOG (d.clause, "new critical clause with weight %f", d.weight);
  assert (d.critical == (unsigned)internal->vidx(lit));
  critical_sat_weight (lit) += d.weight;
}

void Walker_DDFW::make_clauses_along_occurrences (int lit) {
  const auto &occs = this->occs (lit);
  LOG ("making clauses with %s along %zu occurrences", LOGLIT (lit),
       occs.size ());
  assert (internal->val (lit) > 0);
  size_t made = 0;
  ticks += (1 + internal->cache_lines (occs.size (), sizeof (Clause *)));

  for (auto c : occs) {
#if 0
    // only works if make is after break... but we don't want that
    if (broken.empty()) {
      LOG ("early abort: satisfiable!");
      return;
    }
#endif
    this->make_clause (c, lit);
    made++;
  }
  LOG ("made %zu clauses by flipping %d, still %zu broken", made, lit,
       broken.size ());
  LOG ("made %zu clauses with flipped %s", made, LOGLIT (lit));
  (void) made;
}

void Walker_DDFW::make_clauses_along_unsatisfied (int lit) {
  LOG ("making clauses with %s along %zu unsatisfied", LOGLIT (lit),
       this->broken.size ());
  assert (internal->val (lit) > 0);
  size_t made = 0;
  // TODO flush made clauses from 'unsatisfied' directly.
  // TODO 'stats.make_visited++', 'made++' appropriately.
  size_t j = 0;
  const size_t size = this->broken.size ();
  ticks +=
      (1 + internal->cache_lines (this->broken.size (), sizeof (Clause *)));
  for (size_t i = 0, j = 0; i < size; ++i) {
    assert (i >= j);
    const auto &c = this->broken[i];
    assert (c.counter_pos < weight_clause_info.size ());
    DDFW_Counter &d = this->clause_info (c.counter_pos);
    this->broken[j++] = this->broken[i];
    assert (d.pos != invalid_position);
    ++ticks;
    for (auto other : *d.clause) {
      if (lit == other) {
        ++made;
        --j;
        ++d.count;
        LOG (d.clause, "made with count %d", d.count);
        d.pos = invalid_position;
        break;
      }
    }
    if (d.pos != invalid_position)
      LOG (d.clause, "still broken");
    assert (made + j == i + 1); // assertions holds after incrementing 'i'
  }
  assert (j <= size);
  this->broken.resize (j);
  LOG ("made %zu clauses with flipped %s", made, LOGLIT (lit));
  (void) made;
}

void Walker_DDFW::make_clauses (int lit) {
  START (walkflipWL);
  const int64_t old = ticks;
  // In babywalk this work because there are not counter
  // if (this->occs(lit).size() > broken.size())
  //   make_clauses_along_unsatisfied(lit);
  // else
  make_clauses_along_occurrences (lit);
  internal->stats.ticks.walkflipWL += ticks - old;
  STOP (walkflipWL);
}

void Walker_DDFW::break_clauses (int lit) {
  START (walkflipbroken);
  const int64_t old = ticks;
  LOG ("breaking clauses on %s", LOGLIT (lit));
  // Finally add all new unsatisfied (broken) clauses.

#ifdef LOGGING
  size_t broken = 0;
#endif
  const Walker_DDFW::TOccs &ws = occs (lit);
  ticks += (1 + internal->cache_lines (ws.size (), sizeof (Clause *)));

  LOG ("trying to break %zd clauses", ws.size ());

  for (const auto &w : ws) {
    size_t pos = w.counter_pos;
    assert (pos < weight_clause_info.size ());
    DDFW_Counter &d = clause_info (pos);
    const int old_critical = d.critical;
    d.critical ^= internal->vidx (lit);
#ifndef NDEBUG
    LOG (d.clause, "trying to break");
#endif
    --d.count;
    // new critical
    if (d.count == 1) {
      critical_sat_weight(d.critical) += d.weight;
      continue;
    }
    // still satisfied
    if (d.count)
      continue;
    LOG (d.clause, "new broken clause with weight %f", d.weight);
    critical_sat_weight(old_critical) -= d.weight;
    d.pos = this->broken.size ();
    ++ticks;
    this->broken.push_back (w);
    for (auto lit : *d.clause) {
      add_uvar(lit);
      critical_unsat_weight(lit) += d.weight;
    }
#ifdef LOGGING
    broken++;
#endif
  }
  LOG ("broken %zd clauses by flipping %d", broken, lit);
  internal->stats.ticks.walkflipbroken += ticks - old;
  STOP (walkflipbroken);
}

void Walker_DDFW::walk_ddfw_flip_lit (int lit) {
  START (walkflip);
  internal->require_mode (internal->WALK);
  LOG ("flipping assign %d", lit);
  assert (internal->val (lit) < 0);
  assert (internal->active (lit));
  const int64_t old = ticks;

  // First flip the literal value.
  //
  const signed char tmp = sign (lit);
  const int idx = abs (lit);
  internal->set_val (idx, tmp);
  assert (internal->val (lit) > 0);

  make_clauses (lit);
  break_clauses (-lit);

  internal->stats.ticks.walkflip += ticks - old;
  STOP (walkflip);
}

/*------------------------------------------------------------------------*/

size_t Walker_DDFW::maximum_weight_neighbor (Clause *c) {
  size_t max_clause = invalid_position;
  double max_weight = std::numeric_limits<double>::min ();
  ++ticks;
  for (auto lit : *c) {
    ticks +=
        (1 + internal->cache_lines (occs (lit).size (), sizeof (Clause *)));
    for (auto c : occs (lit)) {
      assert (c.counter_pos < weight_clause_info.size ());
      DDFW_Counter neighbor = clause_info (c.counter_pos);
      assert (neighbor.clause);
      if (!neighbor.count)
        continue;
      if (max_clause == invalid_position || neighbor.weight > max_weight)
        max_clause = c.counter_pos;
    }
  }
  return max_clause;
}

size_t Walker_DDFW::random_satisfied_big_weight_clause (double w_0) {
  size_t max_clause = invalid_position;
  bool use_weight_condition = true;
  while (max_clause == invalid_position) {
    size_t pos = random.pick_int(0, weight_clause_info.size ()-1);
    assert (pos < weight_clause_info.size ());
    const DDFW_Counter &c = clause_info (pos);
    if (!c.count)
      continue;
    LOG ("searching at position %zd with weight %f < %f = %d", pos, c.weight, w_0, c.weight < w_0);
    if (use_weight_condition && c.weight < w_0)
      continue;
    max_clause = pos;
  }
  return max_clause;
}

// side remark: we assume that there is a variable to flip without loss. In
// yal-lin, the functions also handles the case there is no such variable, but
// the assumptions is checked before the function call.
void Walker_DDFW::do_sideways_jump () {
  assert (!no_gain_literals.empty ());
  size_t pos = random.pick_int(0, no_gain_literals.size() - 1);
  int lit = no_gain_literals[pos];
  walk_ddfw_flip_lit (lit);
  push_flipped (lit);
  internal->stats.walk.flips++;
  internal->stats.walk.broken += broken.size ();
  ++internal->stats.walk.sideways;
}

void Walker_DDFW::transfer_weights () {
  START(walktransferweights);
  LOG ("transfering weights");
  const double cspt = 0.1;   // probability to choose random satisfied clause
  const double c_big = 2.0;   // big weight increase factor
  const double c_small = 1.0; // small weight increase factor

  ++internal->stats.walk.weight_transfer;
  ticks +=
      (1 + internal->cache_lines (broken.size (), sizeof (DDFW_Tagged)));
  for (auto c : broken) {
    assert (c.counter_pos < weight_clause_info.size ());
    DDFW_Counter &robber = clause_info (c.counter_pos);
    LOG (robber.clause, "transfering weight to");
    assert (robber.clause);
    size_t robbed_pos = maximum_weight_neighbor (robber.clause);
    double p = random.generate_double();
    // TODO: the code does not have this condition on weights
    if (robbed_pos == invalid_position || /*clause_info (robbed_pos).weight < w_0 ||*/ p < cspt)
      robbed_pos = random_satisfied_big_weight_clause (w_0);
    // TODO does this really trigger?
    if (robbed_pos == invalid_position)
      continue;
    assert (robbed_pos < weight_clause_info.size ());
    DDFW_Counter &robbed = clause_info (robbed_pos);
    assert (robbed_pos != c.counter_pos);

    double coeff_a;
    double coeff_c ;
    if (robbed.weight == w_0) {
      coeff_a = 1; // initpct
      coeff_c = 0;
    } else {
      coeff_a = 0.075; // currpct
      coeff_c = 0.167 * w_0; // baspct
    }
    // this is the linear transfer function from the paper. The original ddfw
    // implementation had actually coeff_a == 0 and `coeff_c == robbed.weight >
    // w_0 ? c_big : c_small` with the inverted small/big !
    //
    // The idea of the condition `robbed.weight > w_0` is to initially transfer
    // more weights and later less.
#if 0
    const bool weight_larger = (robbed.weight > w_0);
    switch (internal->opts.walkddfwstrat) {
      case 0: // lw-itl
        coeff_a = weight_larger ? 0.1 : 0.05;
        coeff_c = weight_larger ? 2 : 1;
        break;
      case 1: // lw-ite
        coeff_a = 0.075;
        coeff_c = 1.75;
        break;
      case 2: //lw-ith
        coeff_a = weight_larger ? 0.05 : 0.10;
        coeff_c = weight_larger ? c_small : c_big;
        break;
      default: // original ddfw
        coeff_a = 0;
        coeff_c = weight_larger ? c_big : c_small;
        break;
    }
#endif
    double weight_difference = robbed.weight * coeff_a + coeff_c;
    robber.weight += weight_difference;
    robbed.weight -= weight_difference;
    LOG (robbed.clause, "transfering weight (removing %.3f to get %.3f) from", weight_difference, robbed.weight);
    update_unsat_weights (c.counter_pos, weight_difference);
    update_sat_weights (robbed_pos, weight_difference);
  }
  STOP(walktransferweights);
}

void Walker_DDFW::update_unsat_weights (size_t pos, double weight_difference) {
  assert (pos < weight_clause_info.size ());
  assert (!clause_info (pos).count);
  ++ticks;
  for (auto lit : *clause_info (pos).clause) {
    critical_unsat_weight (lit) += weight_difference;
  }
}
void Walker_DDFW::update_sat_weights (size_t pos, double weight_difference) {
  assert (pos < weight_clause_info.size ());
  assert (clause_info (pos).count);
  if (clause_info (pos).count != 1)
    return;
  unsigned var = clause_info (pos).critical;
  critical_sat_weight (var) -= weight_difference;
}

/*------------------------------------------------------------------------*/

// Check whether to save the current phases as new global minimum.

inline void Internal::walk_ddfw_save_minimum (Walker_DDFW &walker) {
  size_t broken = walker.broken.size ();
  if (broken >= walker.minimum)
    return;
  if (broken <= stats.walk.minimum) {
    stats.walk.minimum = broken;
    VERBOSE (3, "new global minimum %zd", broken);
  } else {
    VERBOSE (3, "new walk minimum %zd", broken);
  }

  walker.minimum = broken;

#ifndef NDEBUG
  for (auto i : vars) {
    const signed char tmp = vals[i];
    if (tmp)
      phases.saved[i] = tmp;
  }
#endif

  if (walker.best_trail_pos == -1) {
    for (auto i : vars) {
      const signed char tmp = vals[i];
      if (tmp) {
        walker.best_values[i] = tmp;
#ifndef NDEBUG
        assert (tmp == phases.saved[i]);
#endif
      }
    }
    walker.best_trail_pos = 0;
  } else {
    walker.best_trail_pos = walker.flips.size ();
    LOG ("new best trail position %u", walker.best_trail_pos);
  }
}

/*------------------------------------------------------------------------*/

// In a departure from the yal-lin implementation we remember where we found a
// literal for the last time and start from here. Unlike the cache for
// propagations, we do not save a quadratic effort, because we have to go
// through all literals anyway. However, this is an attempt to flip in a more
// fair way (first literals with the same probability as the last literals), as
// we pick the first reached minimum.
std::pair<int,double> Walker_DDFW::find_weight_reducing_variable () {
  START (walkwrv);
  int weight_reducing_var = 0;
  double mini_weight_reduction = 0.0;
  int loop_iterations = 0;
  no_gain_literals.clear ();
  const auto begin = vars_in_broken.begin ();
  const auto end = vars_in_broken.end ();
  const auto mid = last_searched_vars_in_broken < vars_in_broken.size () ? vars_in_broken.begin () + last_searched_vars_in_broken : vars_in_broken.end ();
  for (auto it = mid; it != end; ++it) {
    const int idx = *it;
    double flip_gain = critical_sat_weight (idx) - critical_unsat_weight (idx);
    LOG ("considering flipping %s gives %.3f", LOGLIT (idx), flip_gain);
    if (flip_gain < mini_weight_reduction) {
      mini_weight_reduction = flip_gain;
      weight_reducing_var = idx;
      ++loop_iterations;
      last_searched_vars_in_broken = std::distance (begin, it);
      assert (begin <= it);
    }
#if 0
    else if (flip_gain == 0) {
      no_gain_literals.push_back (internal->val (idx) > 0 ? - idx : idx);
    }
#endif
  }
  for (auto it = vars_in_broken.begin (); it != mid; ++it) {
    const int idx = *it;
    double flip_gain = critical_sat_weight (idx) - critical_unsat_weight (idx);
    LOG ("considering flipping %s gives %.3f", LOGLIT (idx), flip_gain);
    if (flip_gain < mini_weight_reduction) {
      mini_weight_reduction = flip_gain;
      weight_reducing_var = idx;
      ++loop_iterations;
      last_searched_vars_in_broken = std::distance (begin, it);
      assert (begin <= it);
    }
#if 0
    else if (flip_gain == 0) {
      no_gain_literals.push_back (internal->val (idx) > 0 ? - idx : idx);
    }
#endif
  }
  ticks += internal->cache_lines (vars_in_broken.size (), sizeof (int)) + loop_iterations / 64;
  if (weight_reducing_var && internal->val (weight_reducing_var) > 0)
    weight_reducing_var = -weight_reducing_var;

  LOG ("deciding to flip %s gives %.3f", LOGLIT (weight_reducing_var), mini_weight_reduction);
  STOP (walkwrv);
  return make_pair (weight_reducing_var, mini_weight_reduction);
}
/*------------------------------------------------------------------------*/

int Internal::walk_ddfw_round (int64_t limit, bool prev) {

  stats.walk.count++;

  std::vector<int> propagated;
  bool failed = false; // Inconsistent assumptions?
  assert (!private_steps);
  int res = decide_and_propagate_all_assumptions (propagated);
  if (res) {
    failed = true;
    return res;
  }
  reset_watches ();

  // Remove all fixed variables first (assigned at decision level zero).
  //
  if (last.collect.fixed < stats.all.fixed)
    garbage_collection ();

#ifndef QUIET
  // We want to see more messages during initial local search.
  //
  if (localsearching) {
    assert (!force_phase_messages);
    force_phase_messages = true;
  }
#endif

  PHASE ("walk", stats.walk.count,
         "random walk limit of %" PRId64 " ticks", limit);

  PHASE ("walk", stats.walk.count,
         "%zd clauses over %d variables", clauses.size (),
         active ());

  // Instantiate data structures for this local search round.
  //
  Walker_DDFW walker (internal, limit);


  level = 1; // Assumed variables assigned at level 1.

  if (failed) {
    LOG ("assumptions are inconsistent");
  } else if (assumptions.empty ()) {
    LOG ("no assumptions so assigning all variables to decision phase");
  } else {
    LOG ("assigning assumptions and their propagations to their forced phase first");
    for (const auto lit : propagated) {
      signed char tmp = val (lit);
      if (tmp > 0)
        continue;
      assert (tmp == 0);
      if (!active (lit))
        continue;
      tmp = sign (lit);
      const int idx = abs (lit);
      LOG ("initial assign %d to assumption phase", tmp < 0 ? -idx : idx);
      set_val (idx, tmp);
      assert (level == 1);
      var (idx).level = 1;
    }
    if (!failed)
      LOG ("now assigning remaining variables to their decision phase");
  }

  level = 2; // All other non assumed variables assigned at level 2.

  if (!failed) {
    const bool target = opts.warmup ? false : stable || opts.target == 2;
    for (auto idx : vars) {
      if (!active (idx)) {
        LOG ("skipping inactive variable %d", idx);
        continue;
      }
      if (vals[idx]) {
        assert (var (idx).level == 1);
        LOG ("skipping assumed variable %d", idx);
        continue;
      }
      int tmp = 0;
      if (prev)
        tmp = phases.prev[idx];
      if (!tmp)
        tmp = sign (decide_phase (idx, target));
      assert (tmp == 1 || tmp == -1);
      set_val (idx, tmp);
      assert (level == 2);
      var (idx).level = 2;
      walker.best_values[idx] = tmp;
      LOG ("initial assign %d to decision phase", tmp < 0 ? -idx : idx);
    }

    LOG ("watching satisfied and registering broken clauses");
#ifdef LOGGING
    int64_t watched = 0;
#endif
    walker.var_critical_sat_weights.resize (internal->max_var+1, 0);
    walker.var_unsat_weights.resize (internal->max_var+1, 0);
    walker.noccs_vars_in_broken.resize (internal->max_var+1, 0);
    walker.noccs_vars_in_broken.resize (internal->max_var+1, 0);
    const size_t i = walker.invalid_position; // I get a compilation error otherwise
    walker.position_vars_in_broken.resize (internal->max_var+1, i);

    for (const auto c : clauses) {
      if (c->garbage)
        continue;
      if (c->redundant) {
        if (!opts.walkredundant)
          continue;
        if (!likely_to_be_kept_clause (c))
          continue;
      }
      LOG (c, "checking clause");
      bool satisfiable = false; // contains not only assumptions
      unsigned satisfied = 0;        // clause satisfied?

      int *lits = c->literals;
      const int size = c->size;
      unsigned critical = 0;

      // Move to front satisfied literals and determine whether there
      // is at least one (non-assumed) literal that can be flipped.
      //
      for (int i = 0; i < size; i++) {
        const int lit = lits[i];
        assert (active (lit)); // Due to garbage collection.
        if (val (lit) > 0) {
          critical ^= internal->vidx (lit);
          swap (lits[satisfied], lits[i]);
          if (!satisfied++)
            LOG ("first satisfying literal %d", lit);
        } else if (!satisfiable && var (lit).level > 1) {
          LOG ("non-assumption potentially satisfying literal %d", lit);
          satisfiable = true;
        }
      }

      if (!satisfied && !satisfiable) {
        LOG (c, "due to assumptions unsatisfiable");
        LOG ("stopping local search since assumptions falsify a clause");
        failed = true;
        break;
      }

      assert (satisfied <= (size_t)c->size);
      size_t pos = walker.weight_clause_info.size ();
      DDFW_Counter cw = DDFW_Counter (satisfied, walker.invalid_position, critical, c, Walker_DDFW::w_0);
      LOG ("found %zd clauses so far, it has %d satisfied literals", pos, satisfied);
      walker.weight_clause_info.push_back (cw);
#ifdef LOGGING
      assert (walker.weight_clause_info.size () == pos + 1);
      assert (pos == watched + walker.broken.size ());
      assert (walker.weight_clause_info[pos].count <= (size_t)c->size);
#endif
      walker.connect_clause (c, pos);

      if (!satisfied) {
        assert (satisfiable); // at least one non-assumed variable ...
        LOG (c, "broken");
        assert (pos < walker.weight_clause_info.size ());
        walker.clause_info(pos).pos = walker.broken.size ();
        walker.broken.push_back (DDFW_Tagged (c, pos));
        ++walker.ticks;
        for (auto lit : *c) {
          walker.critical_unsat_weight (lit) += cw.weight;
          walker.add_uvar (lit);
        }
      } else if (satisfied == 1) {
        walker.critical_sat_weight (critical) += cw.weight;
#ifdef LOGGING
        watched++; // to be able to compare the number with walk
#endif
      }
      else {
#ifdef LOGGING
        watched++; // to be able to compare the number with walk
#endif
      }
    }
#ifdef LOGGING
    if (!failed) {
      size_t broken = walker.broken.size ();
      size_t total = watched + broken;
      LOG ("watching %" PRId64 " clauses %.0f%% "
           "out of %zd (watched and broken)",
           watched, percent (watched, total), total);
    }
#endif
  }

  if (!failed) {
    walker.check_all ();

    size_t broken = walker.broken.size ();
    size_t initial_minimum = broken;

    PHASE ("walk", stats.walk.count,
           "starting with %zd unsatisfied clauses "
           "(%.0f%% out of %" PRId64 ")",
           broken, percent (broken, stats.current.irredundant),
           stats.current.irredundant);

    walk_ddfw_save_minimum (walker);
    assert (stats.walk.minimum <= walker.minimum);

    size_t minimum = broken;
#ifndef QUIET
    int64_t flips = 0;
#endif
    const double sideways_percent = 0.15;    // probability for sideways flips

    while (!terminated_asynchronously () && !walker.broken.empty () &&
           walker.ticks < walker.limit) {
#ifndef QUIET
      flips++;
#endif
#ifndef NDEBUG
      //useful for debugging, but really really really expensive
      if (internal->stats.walk.flips % 100 == 000)
        walker.check_all();
#endif

      broken = walker.broken.size ();
      LOG ("now have %zd broken clauses in total", broken);
      if (broken < minimum) {
        minimum = broken;
        VERBOSE (3, "new phase minimum %zd after %" PRId64 " flips",
               minimum, flips);
        walk_ddfw_save_minimum (walker);
      }

      // first check if there is a weight reducing variable
      auto result = walker.find_weight_reducing_variable ();
      int weight_reducing_lit = result.first;
      double weight_reduction = result.second;

      if (weight_reducing_lit && weight_reduction < 0.0) {
        ++stats.walk.weight_reducing_var;
        LOG ("flipping one literal");
        walker.walk_ddfw_flip_lit (weight_reducing_lit);
        walker.push_flipped (weight_reducing_lit);
        stats.walk.flips++;
        stats.walk.broken += broken;
        continue;
      }
#if 0
      // otherwise, do a sideways flip with low probability
      double perc = walker.random.generate_double ();
      if (!walker.no_gain_literals.empty () && perc < sideways_percent) {
        walker.do_sideways_jump ();
        continue;
      }
#endif
      // transfer weights
      walker.transfer_weights ();
    }

    walker.save_final_minimum (initial_minimum);
#ifndef QUIET
    if (minimum == initial_minimum) {
      PHASE ("walk", internal->stats.walk.count,
             "%sno improvement %zd%s in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             tout.bright_yellow_code (), minimum, tout.normal_code (),
             flips, walker.ticks);
    } else {
      PHASE ("walk", internal->stats.walk.count,
             "best phase minimum %zd in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             minimum, flips, walker.ticks);
    }
#endif

    if (opts.profile >= 2) {
      PHASE ("walk", stats.walk.count, "%.2f million ticks per second",
             1e-6 *
                 relative (walker.ticks, time () - profiles.walk.started));

      PHASE ("walk", stats.walk.count, "%.2f thousand flips per second",
             relative (1e-3 * flips, time () - profiles.walk.started));

    } else {
      PHASE ("walk", stats.walk.count, "%.2f ticks", 1e-6 * walker.ticks);

      PHASE ("walk", stats.walk.count, "%.2f thousand flips", 1e-3 * flips);
    }

    if (minimum > 0) {
      LOG ("minimum %zd non-zero thus potentially continue",
           minimum);
      res = 0;
    } else {
      LOG ("minimum is zero thus stop local search");
      res = 10;
    }

  } else {

    res = 20;

    PHASE ("walk", stats.walk.count,
           "aborted due to inconsistent assumptions");
  }

  for (auto idx : vars)
    if (active (idx))
      set_val (idx, 0);

  assert (level == 2);
  level = 0;

  init_watches ();
  connect_watches ();

#ifndef QUIET
  if (localsearching) {
    assert (force_phase_messages);
    force_phase_messages = false;
  }
#endif
  stats.ticks.walk += walker.ticks;
  return res;
}

void Internal::walk_ddfw () {
  START_INNER_WALK ();

  backtrack ();
  if (propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after root level propagation");
    learn_empty_clause ();
    STOP_INNER_WALK ();
    return;
  }

  int res = 0;
  if (opts.warmup)
    res = warmup ();
  if (res) {
    LOG ("stopping walk due to warmup");
    STOP_INNER_WALK ();
    return;
  }
  const int64_t ticks = stats.ticks.search[0] + stats.ticks.search[1];
  int64_t limit = ticks - last.walk.ticks;
  VERBOSE (2,
           "walk scheduling: last %" PRId64 " current %" PRId64
           " delta %" PRId64,
           last.walk.ticks, ticks, limit);
  last.walk.ticks = ticks;
  limit *= 1e-3 * opts.walkeffort;
  if (limit < opts.walkmineff)
    limit = opts.walkmineff;
  // local search is very cache friendly, so we actually really go over a
  // lot of ticks
  if (limit > 1e3 * opts.walkmaxeff) {
    MSG ("reached maximum efficiency %" PRId64, limit);
    limit = 1e3 * opts.walkmaxeff;
  }
  (void) walk_ddfw_round (limit, false);
  STOP_INNER_WALK ();
}

} // namespace CaDiCaL
