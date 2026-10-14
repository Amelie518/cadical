#include "internal.hpp"
#include "clause.hpp"
#include <vector>

int size = 1000;
namespace CaDiCal {

bool encode (Internal *internal, std::vector<Clause *> clauses, const std::vector<signed char> &autarky_val,
    signed char *assignment, signed char *cadical_autarkie) {
    // int for every literal of assignment
    // positive if chosen for max autarkie, negative if not
    std::vector<int> select(size + 1, 0); //hätte hier max_var genommen, aber keine zugriff drauf, assigment als vector
    int num_var = 1;
    //initializes select for every relevant val with a number staring with 0
    for (size_t s = 1; s < autarky_val.size(); s++) { //autarky_val.size macht glaueb ich keinen sinn, muss eigentllich die größe des assignments sein
        if (autarky_val[s] != 0) {
            select[s] = num_var;
            num_var++;
        }
    }
    std::vector<std::vector<int>> encoded_clauses;
    
    //encoding autarkie
    for (auto *c: clauses) {
        std::vector<int> satisfied; //passt int? oder char
        std::vector<int> falsified;
        for (auto l: *c) {
            if (autarky_val[internal->vlit(l)] == 1)  {//satisfies clause
                satisfied.push_back(abs(l)); // will ich lit oder abs lit
            } else if (autarky_val[vlit(l)] == -1) 
                falsified.push_back(abs(l));
        }
        for (auto f:falsified) {
            //not select[f] or all select[s] from satisfied
            std::vector<int> clause;
            clause.push_back(-select[f]);
            for (auto s:satisfied) {
                clause.push_back(select[s]);
            }
            encoded_clauses.push_back(clause);
        }
    }

    //max(sum(select(abs))))

    //sat solver? belegung(lösung) von sat solver

    //return autarky with all lits that are positive in the belegung
}
}