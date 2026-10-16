#include <vector>
#include <cstdlib>
#include <cstdio>
#include <sstream>
#include <stdexcept>
#include <string>
#include <iostream>
#include <fstream>
#include <unordered_map>

//checks wether literal of clause satisfies clause
int satisfying_literal(int lit, const std::vector<int> &assignment) {
    for (int a: assignment) {
        if (abs(a) == abs(lit)) {
            if ((a > 0) == (lit > 0))
                return 1;
            else return -1;
        }
    }
    return 0;
}

void encode (std::vector<std::vector<int>> &clauses,
    std::vector<int> &assignment, std::vector<int> &cadical_autarkie) {
    // int for every literal of assignment
    // positive if chosen for max autarkie, negative if not
    std::unordered_map<int, int> select;
    int num_var = 1;
    //initializes select for every relevant val with a number staring with 1
    for (int lit: assignment) {
        int var = abs(lit);
        if (select.find (var) == select.end()) {
            select[var] = num_var;
            num_var++;
        }
    }
    std::vector<std::vector<int>> encoded_clauses;
    
    //encoding autarkie
    for (auto c: clauses) {
        std::vector<int> satisfied;
        std::vector<int> falsified;
        for (auto l: c) {
            int sat_lit = satisfying_literal(l, assignment);
            if (sat_lit == 1)  {//satisfies clause
                satisfied.push_back(abs(l));
            } else if (sat_lit == -1) 
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

struct InputData {
    std::vector<int> assignment;
    std::vector<int> cadical_autarkie;
    std::vector<std::vector<int>> clauses;
};

InputData read_input(const std::string& filename) {
    InputData data;

    // Prüfen, ob die Datei tatsächlich XZ-komprimiert ist.
    std::ifstream check(filename, std::ios::binary);
    if (!check)
        throw std::runtime_error("Datei konnte nicht geöffnet werden");

    unsigned char magic[6] = {};
    check.read(reinterpret_cast<char*>(magic), 6);

    bool compressed =
        check.gcount() == 6 &&
        magic[0] == 0xFD &&
        magic[1] == 0x37 &&
        magic[2] == 0x7A &&
        magic[3] == 0x58 &&
        magic[4] == 0x5A &&
        magic[5] == 0x00;

    check.close();

    FILE* pipe = nullptr;
    std::ifstream file;

    if (compressed) {
        std::string command = "xz -dc -- '" + filename + "'";
        pipe = popen(command.c_str(), "r");

        if (!pipe)
            throw std::runtime_error("Datei konnte nicht entpackt werden");
    } else {
        file.open(filename);

        if (!file)
            throw std::runtime_error("Datei konnte nicht geöffnet werden");
    }

    enum class State {
        Normal,
        ReadAssignment,
        ReadCadicalAutarkie
    };

    State state = State::Normal;
    std::vector<int> current_clause;

    // Verarbeitung einer einzelnen Zeile
    auto process_line = [&](const std::string& line) {
        std::istringstream iss(line);
        std::string first;

        if (!(iss >> first))
            return;

        if (first == "c") {
            std::string comment;
            std::getline(iss, comment);

            if (comment.find("starting point") != std::string::npos) {
                state = State::ReadAssignment;
                return;
            }

            if (comment.find("final autarky") != std::string::npos) {
                state = State::ReadCadicalAutarkie;
                return;
            }

            if (comment.find("end autarky") != std::string::npos) {
                state = State::Normal;
                return;
            }

            // Die Kommentarzeile nach dem Marker enthält die Literale.
            if (state == State::ReadAssignment ||
                state == State::ReadCadicalAutarkie) {

                std::istringstream literals(comment);
                int lit;

                while (literals >> lit) {
                    if (lit == 0)
                        continue;

                    if (state == State::ReadAssignment)
                        data.assignment.push_back(lit);
                    else
                        data.cadical_autarkie.push_back(lit);
                }

                state = State::Normal;
            }

            return;
        }

        // DIMACS-Kopfzeile überspringen
        if (first == "p")
            return;

        // Klauseln einlesen
        if (state == State::Normal) {
            std::istringstream literals(line);
            int lit;

            while (literals >> lit) {
                if (lit == 0) {
                    data.clauses.push_back(current_clause);
                    current_clause.clear();
                } else {
                    current_clause.push_back(lit);
                }
            }
        }
    };

    if (compressed) {
        char buffer[65536];
        std::string line;

        while (fgets(buffer, sizeof(buffer), pipe)) {
            line += buffer;

            // Lange Zeilen erst verarbeiten, wenn sie vollständig sind.
            if (!line.empty() && line.back() == '\n') {
                process_line(line);
                line.clear();
            }
        }

        if (!line.empty())
            process_line(line);

        int status = pclose(pipe);

        if (status != 0)
            throw std::runtime_error("Fehler beim Lesen der XZ-Datei");
    } else {
        std::string line;

        while (std::getline(file, line))
            process_line(line);
    }

    if (!current_clause.empty())
        data.clauses.push_back(current_clause);

    return data;
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Verwendung: " << argv[0] << " <datei.cnf.xz>\n";
        return 1;
    }

    InputData input = read_input(argv[1]); 

    std::cout << "Assignment-Literale: "
              << input.assignment.size() << '\n';

    std::cout << "CaDiCaL-Autarkie-Literale: "
              << input.cadical_autarkie.size() << '\n';

    std::cout << "Klauseln: "
              << input.clauses.size() << '\n';

    
    encode(input.clauses, input.assignment, input.cadical_autarkie);

    return 0;
}