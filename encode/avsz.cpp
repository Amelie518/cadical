#include <iostream>
#include <fstream>
#include <string>
#include <map>
#include <cctype>

int main (int argc, char* argv[]) {
    if (argc< 2) {
        std::cout << "usage: ./avsz.cpp 'filename.log'" << std::endl;
        return 1;
    }

    std::ifstream file (argv[1]);
    std::map<char, int> results_a;
    std::map<char, int> results_z;
    std::string line;
    char last_upper = 0;
    while(getline(file,line)) {
        if (line.size() < 2 || line[0] != 'c' || line[1] != ' ')
            continue;
        char marker = line[2];
        if (isupper(marker) || marker == '#') {
            last_upper = marker;
        }
        else if (marker = 'a') {
            if (last_upper != '0') {
                results_a[last_upper]++;
            }
        }
        else if (marker = 'z') {
            if (last_upper != '0') {
                results_z[last_upper]++;
            }
        }
    }
    std::cout << "results for a" << std::endl;
    for (auto entry: results_a) {
        std::cout << entry.first << ": " << entry.second << std::endl;
    }
    std::cout << "results for z" << std::endl;
    for (auto entry: results_z) {
        std::cout << entry.first << ": " << entry.second << std::endl;
    }
    return 0;
}