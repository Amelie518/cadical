#include <vector>
#include <cstdlib>
#include <cstdio>
#include <sstream>
#include <stdexcept>
#include <string>
#include <iostream>
#include <fstream>
#include <unordered_map>

int main (int argc, char *argv[]) {
	if (argc < 2) {
		std::cerr << "Verwendung: " << argv[0] << " <datei.log>\n";
        return 1;
	}
	std::ifstream file (argv[1]);
	if (!file) {
		std::cerr << "Datei konnte nicht geöffnet werden\n";
		return 1;
	}

	std::string line;
	int true_vars = 0;
	int false_vars = 0;
	int cadical_autarky_size;
	std::ifstream size_file("cadical_autarky_size.log");
	if (!file) {
		std::cerr << "Autarky size konnte nicht geöffnet werden\n";
		return 1;
	}

	while (std::getline(file, line)) {
		if (line.empty() || line[0] != 'v')
			continue;
		std::string rest = line.substr(1);
		int lit;
		std::istringstream input(rest);
		while (input >> lit && lit != 0) {
			if (lit>=0)
				true_vars++;
			else 
				false_vars++;
		}
	}
	std::cout <<"true variables: " << true_vars << "\n";
	std::cout <<"autarky variables: " << cadical_autarky_size << "\n";
	std::cout <<"false variables: " << false_vars << "\n";

	return 0;
}