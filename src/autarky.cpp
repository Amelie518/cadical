#include "internal.hpp"
#include <map>
namespace CaDiCaL {
// Algorithm to find autarkies based on the phases.  For incremental SAT solving, this can be a
// bootleneck, because the witness for the reconstruction stack can be huge.
inline unsigned Internal::autarky_propagate_clause (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work) {
  assert (!c->redundant);
  assert (!c->garbage);
  assert (!level);
  bool satisfied = false;
  bool falsified = false;
  unsigned unassigned = 0;
  LOG (c, "autarky checking clause");
  for (auto lit : *c) {
    const int idx = abs (lit);
    if (frozen (idx))
      continue;
    if (val (lit) > 0) {
      LOG ("removing satisfied clause");
      mark_garbage(c);
      return 0;
    }
    if (val (lit) < 0)
      continue;

    const int v = autarky_val[vlit (lit)];
    if (v > 0)
      satisfied = true;
    else if (v < 0) {
      falsified = true;
    }
  }

  if (satisfied)
    return 0;
  if (!falsified)
    return 0;
  LOG ("clause is falsified and not satisfied, removing all set literals");

  for (auto lit : *c) {
    if (frozen (lit))
      continue;
    if (val (lit) < 0)
      continue;
    const int v = autarky_val[vlit (lit)];
    if (!v)
      continue;
    assert (v < 0);
    LOG ("unassigning lit %d", lit);
    autarky_val[vlit (lit)] = autarky_val[vlit (-lit)] = 0;
    work.push_back (-lit);

    ++unassigned;
  }
  assert (unassigned);
  return unassigned;
}

unsigned Internal::autarky_propagate_binary (Clause *c, std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  assert (!c->redundant);
  assert (!c->garbage);
  assert (!level);
  (void) c;
  if (val (lit) > 0)
    return 0;
  const int v = autarky_val[vlit (lit)];
  if (v >= 0) {
    return 0;
  }
  assert (v < 0);
  LOG ("unassigning lit %d", lit);
  autarky_val[vlit (lit)] = autarky_val[vlit (-lit)] = 0;
  work.push_back (-lit);
  return 1;
}

unsigned Internal::autarky_propagate_unassigned (std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  int unassigned = 0;
  assert (autarky_val[vlit (lit)] <= 0);
  const Watches &ws = watches (lit);
  for (auto &w : ws) {
    if (w.clause->garbage)
      continue;
    if (w.clause->redundant)
      continue;
    LOG (w.clause, "autarking working on clause");
    if (w.binary()){
        unassigned += autarky_propagate_binary (w.clause, autarky_val, work, w.blit);
    }
    else
      unassigned += autarky_propagate_clause (w.clause, autarky_val, work);
  }
  return unassigned;
}

unsigned Internal::autarky_propagate_unassigned_binary (std::vector<signed char> &autarky_val, std::vector<int> &work, int lit) {
  int unassigned = 0;
  assert (autarky_val[vlit (lit)] <= 0);
  const Watches &ws = watches (lit);
  for (auto &w : ws) {
    if (w.clause->garbage)
      continue;
    if (w.clause->redundant)
      continue;
    LOG (w.clause, "autarking working on clause");
    if (w.binary()){
        unassigned += autarky_propagate_binary (w.clause, autarky_val, work, w.blit);
    }
  }
  return unassigned;
}

unsigned Internal::autarky_propagate (std::vector<signed char> &autarky_val, std::vector<int> &work) {
  int unassigned = 0;
  while (!work.empty()) {
    const int lit = work.back();
    work.pop_back();
    LOG ("autarky propagating lit %d (%d unassigned)", lit, unassigned);
    unassigned += autarky_propagate_unassigned (autarky_val, work, lit);
  }
  return unassigned;
}


int Internal::determine_autarky (std::vector<signed char> &autarky_val, std::vector<int> &work) {
  unsigned assigned = 0;
  clear_watches ();
  connect_binary_watches ();
  const bool target = false && (opts.target > 1 || (stable && opts.target));
  // importing phases
  for (auto idx : vars) {
    autarky_val[vlit (idx)] = 0;
    autarky_val[vlit (-idx)] = 0;
    if (!flags (idx).active())
      continue;
    if (frozen (idx))
      continue;
    if (val (idx))
      continue;
    signed char v = target ? phases.target[idx] : phases.saved[idx];
    if (!v)
      v = opts.phase ? 1 : -1;
    LOG ("setting initial value of %d to %d", idx, v);
    autarky_val[vlit (idx)] = v;
    autarky_val[vlit (-idx)] = -v;
    assert (autarky_val[vlit (idx)] == -autarky_val[vlit (-idx)]);
    ++assigned;
  }

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  // pre-filtering
  for (auto *c : clauses) {
    if (last_irredundant && c > last_irredundant)
      break;
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;

    const unsigned unassigned = autarky_propagate_clause(c, autarky_val, work);
    if (!unassigned)
      continue;
    assert (unassigned <= assigned);
    assigned -= unassigned;
    if (!assigned)
      break;
  }

  if (assigned) {
    LOG ("preliminary autarky of size %d", assigned);
  } else {
    LOG ("empty autarky");
    clear_watches();
    connect_watches ();
    return false;
  }

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  for (auto lit : lits) {
    if (!assigned)
      break;
    if (!flags(lit).active() || frozen (lit))
      continue;
    const signed char v = autarky_val[vlit (lit)];

    if (v > 0)
      continue;
    // first just do the binary watches for speed
    assigned -= autarky_propagate_unassigned_binary (autarky_val, work, lit);
    //work.push_back(lit);
    assigned -= autarky_propagate (autarky_val, work);
  }

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  if (assigned) {
    LOG ("second stage autarky of size %d", assigned);
  }   else {
    LOG ("empty autarky");
    clear_watches();
    connect_watches ();
    return false;
  }

  // final pass. This requires a full-watched literal scheme.

  for (auto *c : clauses) {
    if (!assigned)
      break;
    if (last_irredundant && c > last_irredundant)
      break;
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    LOG (c, "final checking clause for autarky ");
    unsigned unassigned = autarky_propagate_clause (c, autarky_val, work);
    if (unassigned) {
      assigned -= unassigned + autarky_propagate(autarky_val, work);
    }
    else {
      const int l1 = c->literals[0];
      const int l2 = c->literals[1];
      for (auto lit: *c) {
        const signed char v = autarky_val[vlit (lit)];
        const int other = (lit == l1 ? l2 : l1);
        if (v > 0) {
          Watches &ws = watches (lit);
          ws.push_back (Watch (other, c));
          LOG (c, "watch %d blit %d in", lit, other);
        }
      }
    }
  }

#ifndef NDEBUG
  {
    unsigned i = 0;
    for (auto lit : vars) {
      if (autarky_val[vlit (lit)])
        ++i;
    }
    assert (i == assigned);
  }
#endif

  clear_watches();

  if (assigned) {
    LOG ("found autarky of size %d", assigned);
  } else {
    LOG ("empty autarky");
    connect_watches ();
  }

  return assigned;
}

struct UnionFind {
  std::vector<int> parent;
  // initalising, every variable points to itself
  UnionFind(int n) {
    parent.resize(n+1);
    for (int i = 0; i <= n; ++i) {
      parent[i] = i;
    }
  }
  // returns class (root) of var i
  int find(int i) {
    if (parent[i] == i) return i;
    return parent[i] = find(parent[i]);
  }

  void unite(int i, int j) {
    int root_i = find(i);
    int root_j = find(j);
    if (root_i != root_j) {
      parent[root_i] = root_j;
    }
  }

};

struct Tarjan {
  std::vector<std::unordered_set<int>> &graph;
  std::vector<int> dfs_num;
  std::vector<int> dfs_low;
  std::vector<int> stack;
  std::vector<bool> on_stack;
  int current_dfs_num;
  std::unordered_set<int> active;
  std::vector<std::vector<int>> components;

  Tarjan(std::vector<std::unordered_set<int>> &g, std::unordered_set<int> a)
    : graph(g),
    dfs_num(g.size(), -1),
    dfs_low(g.size(), 0),
    on_stack(g.size(), false),
    current_dfs_num(0),
    active(a) {}

  void dfs(int v) {
    dfs_num[v] = current_dfs_num;
    dfs_low[v] = current_dfs_num;
    current_dfs_num++;
    stack.push_back(v);
    on_stack[v] = true;

    for (int u: graph[v]) {
      if (dfs_num[u] == -1) {
        dfs(u);
        dfs_low[v] = std::min(dfs_low[v], dfs_low[u]);
      } else if (on_stack[u]) {
        dfs_low[v] = std::min(dfs_low[v], dfs_num[u]);
      }
    }
    //found SCC
    if (dfs_low[v] == dfs_num[v]) {
      std::vector<int> component;
      while (true) {
        int u = stack.back();
        stack.pop_back();
        on_stack[u] = false;
        component.push_back(u);
        if(u == v)
          break;
      }
      components.push_back(component);
    }
  }

  void run() {
    for (int i: active) {
      if (dfs_num[i] == -1)
        dfs(i);
    }
  }
};

void Internal::autarky_apply (const std::vector<signed char> &autarky_val,
                              const std::vector<int> &actual_autarky) {                            
  int removed = 0;
  bool compact = opts.autarkynonincr;
  int16_t autarkyalgo = opts.autarkyalgo;
  LOG (actual_autarky, "the autarky is ");
  MSG("max_var = %d", max_var);
  MSG("actual_autarky = %zu", actual_autarky.size());
  std::vector<std::unordered_set<int>> graph(max_var+1);
  std::vector<int> order_of_lit(max_var +1,0);
  std::unordered_map<int, std::vector<int>> order_to_witness_group;

  assert (analyzed.empty ());
  // initialise unionfind
  UnionFind uf(max_var);
  //for every clause unite all vars present in clause                              
  for (auto *c: clauses) {
    if (c->garbage || c-> redundant)
      continue;
    int first_var = 0;
    if (autarkyalgo != 0) {
      //search witness for clause and order literals of autarkie
      if (autarkyalgo == 3) {
        std::vector<int> falsified_vars;
        int sat_var = 0;
        for (auto lit: *c) {
          int v = abs(lit);
          if (autarky_val[vlit(lit)] == 0) // not pat of the autarky
            continue;
          else if (autarky_val[vlit(lit)] > 0) { // literal satisfies clause
            if (sat_var ==0) { // simply choosing first one
              sat_var = v;
            }
          }
          else if (autarky_val[vlit(lit)] < 0) { // literal does not satisfy clause and is dependant on sat_var, has to be after it in order
            falsified_vars.push_back(v);
          }
        }
        //add the literals to graph
        if (sat_var > 0 && !falsified_vars.empty()) {
          for (int false_var: falsified_vars) {
            //if(uf.find(sat_var) == uf.find(false_var)) {
            //  continue; //already in same cycle
            //}
            graph[sat_var].insert(false_var);
          }
        }
      } else {
        for (auto lit: *c) {
          int v = abs(lit);
          if(autarky_val[vlit(lit)] != 0) { //literal does belong to autarky
            if (first_var == 0) {
              first_var = v;
            } else {
              uf.unite(first_var, v);
            }
          }
        }
      }
    int chosen = 0;
    bool covered = false;
    for (auto lit: *c) {
      if (marked (lit) > 0) {
        covered = true;
        assert (autarky_val[vlit(lit)]> 0);
        break;
      }
      if(autarky_val[vlit(lit)] > 0 && chosen == 0) {
        chosen = lit;
      }
    }
    if (!covered && chosen) {
      analyzed.push_back(chosen);
      assert (!marked (chosen));
      mark (chosen);
    }
    }
  }
  int current_order = 1;
  //tarjans algorithm, finding strong connected components (cycles)
  //then generate order list for witness literals via dfs
  if (autarkyalgo == 3) {
    std::unordered_set<int> active;
    for (int lit : actual_autarky)
      active.insert(abs(lit));
    Tarjan tarjan (graph, active);
    tarjan.run();
    MSG("found %zu SCCs", tarjan.components.size());

    //Build SCC grapoh
    std::vector<int> component_id(max_var +1,-1);
    for (size_t i = 0; i< tarjan.components.size(); i++) {
      for (int v: tarjan.components[i]) {
        component_id[v] = i;
      }
    }
    std::vector<std::vector<int>> scc_graph(tarjan.components.size());
    std::vector<int> indegree(tarjan.components.size(), 0);
    for (int u = 1; u <= max_var; u++) {
      for (int v: graph[u]) {
        int cu = component_id[u];
        int cv = component_id[v];
        if (cu != cv) {
          scc_graph[cu].push_back(cv);
        }
      }
    }
    //remove duplicate edges
    for (auto &edges : scc_graph) {
      std::sort(edges.begin(), edges.end());
      edges.erase (std::unique(edges.begin(), edges.end()),edges.end());
      for (int x: edges) {
        indegree[x]++;
      }
    }
    //find topological order
    std::queue<int> queue;
    //int current_order = 1;

    //find start literal (literal with deg = 0)

    for (size_t comp = 0; comp < tarjan.components.size(); comp++) {
      if (indegree[comp] == 0) {
        queue.push(comp);
      }
    }
    while (!queue.empty()) {
      int u = queue.front();
      queue.pop();
      for (int v: tarjan.components[u]) {
        for (auto lit:actual_autarky) {
          if (abs(lit) == v) {
            order_of_lit[v] = current_order;
            order_to_witness_group[current_order].push_back(lit);
            //MSG("layer %d gets literal %d", current_order, lit);
            break;
          }
        }
      }
      for (int next: scc_graph[u]) {
        indegree[next]--;
        if (indegree[next] == 0) {
          queue.push(next);
        }
      }
      current_order++;
      // for (auto &entry : order_to_witness_group) {
      //   MSG("witness layer %d:", entry.first);
      //   for (int lit: entry.second)
      //     MSG(" %d", lit);
      // }
    }
    for (int lit : actual_autarky) {
      int v = abs(lit);
      if (order_of_lit[v] == 0) {
        order_of_lit[v] = current_order;
        order_to_witness_group[current_order].push_back(lit);
      }
    }
    MSG("order %d", current_order);
  }
  for (auto lit : analyzed)
    unmark (lit);

  for (auto lit : lits)
    assert (!marked (lit));

  std::unordered_map<int, std::vector<int>> partitions;
  std::unordered_map<int, std::vector<int>> selected_partitions;
  
  if (autarkyalgo == 1) {
    for (int lit: actual_autarky) {
     int root = uf.find(abs(lit));
     partitions[root].push_back(lit);
    }
    MSG("partition size: %zu", partitions.size());
    if (partitions.size()>1) {
      MSG("Autarky Decompostiton: Split %zu literals into %zu independent omegas", actual_autarky.size(), partitions.size());
      for (const auto &p : partitions)
        MSG("size of %d: %d", p.first, p.second.size ());
    }
    assert (!partitions.empty());
  }
  else if (autarkyalgo == 2) {
    for (auto lit: analyzed) {
      int root = uf.find(abs(lit));
      selected_partitions[root].push_back(lit);
    }
    MSG("partition size: %zu", selected_partitions.size());
    if (selected_partitions.size()>1) {
      MSG("Autarky Decompostiton: Split %zu literals into %zu independent omegas", actual_autarky.size(), selected_partitions.size());
      for (const auto &p : selected_partitions)
      MSG ("size of %d: %d", p.first, p.second.size ());
    }
  }
  if (autarkyalgo != 3) {
    for (auto *c : clauses) {
      if (c->garbage)
        continue;
      int clause_root = -1;
  #ifndef NDEBUG
      bool satisfied = false;
      bool falsified = false;
  #endif
      bool touched = false;
      for (auto lit : *c) {
        const signed char v = autarky_val [vlit (lit)];
        touched = (touched || v);
        clause_root = uf.find(abs(lit));
  #ifndef NDEBUG
        if (v > 0) {
          satisfied = true; break;
        }
        if (v < 0) {
          falsified = true;
          continue;
        }
  #endif
      if (v)
        break;
      }
      LOG (c, "clause");
      assert (c->redundant || !falsified || satisfied);
      assert (c->redundant || touched == satisfied);
      if (c->redundant && touched) {
        LOG (c, "delete touched clause");
        mark_garbage (c);
        continue;
      }
      if (touched) {
        assert (!c->redundant);
        if (!compact) {
          if (proof)
            proof->weaken_minus(c);
          assert(clause_root != -1);
          std::vector<int> witness = actual_autarky;
          if (autarkyalgo ==1)
            witness = partitions[clause_root];
          else if (autarkyalgo == 2)
            witness = selected_partitions[clause_root];
          stats.autarkies.saved += actual_autarky.size()- witness.size();
          external->push_external_clause_and_witness_on_extension_stack(c, std::move (witness));
        }
        LOG (c, "autarky removed satisfied clause");
        mark_garbage (c);
        ++removed;
      }
    }
  }
  else if (autarkyalgo == 3 ) {
    // max order = current order because we stopped counting
    int max_layer = current_order; 
    for (int num = 1; num <= max_layer; ++num) {
      for (auto *c : clauses) {
        if (c->garbage) 
          continue;
        int sat_lit = 0;
  //#ifndef NDEBUG
      bool satisfied = false;
      bool falsified = false;
  //#endif
      bool touched = false;
      for (auto lit : *c) {
        const signed char v = autarky_val [vlit (lit)];
        touched = (touched || v);
        if (v > 0) {
          if (sat_lit == 0 || order_of_lit[abs(lit)] < order_of_lit[abs(sat_lit)]) {
            sat_lit = lit;
          }
        }
  //#ifndef NDEBUG
        if (v > 0) {
          satisfied = true; break;
        }
        if (v < 0) {
          falsified = true;
          continue;
        }
  //#endif
      if (v)
        break;
      }
      LOG (c, "clause");
      assert (c->redundant || !falsified || satisfied);
      assert (c->redundant || touched == satisfied);
      if (c->redundant && touched) {
        LOG (c, "delete touched clause");
        mark_garbage (c);
        continue;
      }
      if (touched && sat_lit != 0) {
        assert (!c->redundant);
        int order = order_of_lit[abs(sat_lit)];
        assert(order > 0);
        assert(num <= order);
        assert(num <= current_order); //current_order is max order
        // Lösche alle Klauseln, deren minimale Erfüllungs-Layer <= num ist
        if (order <= num) {
          if (!compact) {
            if (proof) proof->weaken_minus(c);
            assert(order_to_witness_group.count(order));
            assert(!order_to_witness_group[order].empty());
            std::vector<int> witness = order_to_witness_group[order];
            stats.autarkies.saved += actual_autarky.size() - witness.size();
            external->push_external_clause_and_witness_on_extension_stack(c, std::move(witness));
          }
          mark_garbage(c);
          c->garbage = true;
          ++removed;
        }
      }
      assert(satisfied || !touched);
      }
      int count = 0; 
      for (auto *c : clauses) {
        bool touched = false;
        int order = -1;
        auto sat_lit = 0;
        for (auto lit : *c) {
          const signed char v = autarky_val [vlit (lit)];
          touched = (touched || v);
          if (sat_lit == 0 || order_of_lit[abs(lit)] < order_of_lit[abs(sat_lit)]) {
            sat_lit = lit;
          }
        }
        order = order_of_lit[abs(sat_lit)];
        if (!c->garbage && touched) {
          count++;
          MSG("order of clause %d current num: %d max order: %d", order, num, current_order);
          continue;
        }
      }
      MSG("count of clauses to work on %d", count);
    }
}
  // If a literal does not appear anymore in the formula, it will be part of the autarky, but not appear in any partition.
  if (autarkyalgo == 2)
    assert(!selected_partitions.empty() || !removed);

  MSG ("autarky applied");
  if (compact) {
    for (auto var : vars) {
      const signed char v = autarky_val [vlit (var)];
      if (!v)
        continue;
      assert (v == 1 || v == -1);
      int lit = v * var;
      // fake id!
      external->push_external_clause_and_witness_on_extension_stack({lit}, {lit}, var);
    }
  }
  analyzed.clear ();
  LOG ("autarky removed %d clauses", removed);
}

bool Internal::autarky (char c) {
  if (unsat)
    return false;
  if (level) // conflict during warmup
    return false;
  if (!opts.autarkies)
    return false;
  if (delay->bumpreasons.interval > 10){
    delay->bumpreasons.limit = 0;
    delay->bumpreasons.interval = 10;
  }
  if (opts.autarkydelay && delay_autarky.bumpreasons.delay ()) {
     delay_autarky.bumpreasons.reduce_delay ();
     return false;
  }
  START (autarky);
  START (autarkydetermine);

  std::vector<signed char> autarky_val; autarky_val.resize (2*max_var + 2);
  std::vector<int> work;

  ++stats.autarkies.tries;
  int autarky_found = determine_autarky(autarky_val, work);
  if (!autarky_found){
    delay_autarky.bumpreasons.bump_delay ();
    STOP (autarkydetermine);
    STOP (autarky);
    return false;
  }
  delay_autarky.bumpreasons.reduce_delay ();
  std::vector<int> actual_autarky; actual_autarky.reserve (autarky_found);
  const bool full_aut = !opts.autarkynonincr;

  STOP (autarkydetermine);
  START (autarkyapply);
  for (auto idx : vars) {
    if (!active (idx))
      continue;
    if (!autarky_val [vlit (idx)])
      continue;
    assert (active (idx));
    if (autarky_val [vlit (idx)] > 0){
      if (full_aut) actual_autarky.push_back(idx);
    }
    else {
      assert (autarky_val [vlit (-idx)] > 0);
      assert (autarky_val [vlit (idx)] < 0);
      if (full_aut) actual_autarky.push_back(-idx);
    }
  }
  assert (!full_aut || !actual_autarky.empty ());

  autarky_apply (autarky_val, actual_autarky);


  for (auto idx : vars) {
    if (!autarky_val [vlit (idx)])
      continue;
    assert (active (idx));
    mark_eliminated (idx);
  }
  STOP (autarkyapply);
  ++stats.autarkies.successful;
  stats.autarkies.eliminated += autarky_found;
  //mark_redundant_clauses_with_eliminated_variables_as_garbage ();
  connect_watches();
  report (c);
  STOP (autarky);
  return autarky_found;
}

}
