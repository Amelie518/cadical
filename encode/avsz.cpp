#include <iostream>
#include <fstream>
#include <string>
#include <map>
#include <cctype>
#include <filesystem>

int main (int argc, char* argv[]) {
    if (argc< 2) {
        std::cout << "usage: ./avsz.cpp 'directoryname' optional printwihtfilebool 'true'" << std::endl;
        return 1;
    }
    //if set to true results for a and z get printed for every file individually, otherwise results get accumulated
    bool print_with_file = false;
    if (argc == 3 && std::string(argv[2]) == "true") {
        print_with_file = true;
    }
    std::map<char, int> results_a;
    std::map<char, int> results_z;
    for (auto &entry: std::filesystem::directory_iterator(argv[1])) {
        if (!entry.is_regular_file() || entry.path().extension() != ".log")
            continue;
        std::string filename = entry.path().string();
        std::ifstream file (filename);
        if (!print_with_file) {
            std::map<char, int> results_a;
            std::map<char, int> results_z;
        }
        std::string line;
        char last_upper = '0';
        while(getline(file,line)) {
            if (line.size() < 2 || line[0] != 'c' || line[1] != ' ')
                continue;
            char marker = line[2];
            if ((isupper(marker) || marker == '#') && line[3] == ' ') {
                last_upper = marker;
            }
            else if (marker == 'a') {
                if (last_upper != '0') {
                    results_a[last_upper]++;
                }
            }
            else if (marker == 'z') {
                if (last_upper != '0') {
                    results_z[last_upper]++;
                }
            }
        }
        if (print_with_file) {
            std::cout<< filename << std::endl;
            std::cout << "results for a" << std::endl;
            for (auto entry: results_a) {
                std::cout << entry.first << ": " << entry.second << std::endl;
            }
            std::cout << "results for z" << std::endl;
            for (auto entry: results_z) {
                std::cout << entry.first << ": " << entry.second << std::endl;
            }
        }
    }
    if (!print_with_file) {
            std::cout << "results for a" << std::endl;
            for (auto entry: results_a) {
                std::cout << entry.first << ": " << entry.second << std::endl;
            }
            std::cout << "results for z" << std::endl;
            for (auto entry: results_z) {
                std::cout << entry.first << ": " << entry.second << std::endl;
            }
        }
    return 0;
}