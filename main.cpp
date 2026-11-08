#include <chrono>
#include <iostream>

#include "parser.h"

using namespace CSat;

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: ./output <dimacs_file.cnf>\n";
        return 1;
    }

    std::string filename = argv[1];
    std::cout << "c Parsing " << filename << "...\n";

    auto start_parse = std::chrono::high_resolution_clock::now();
    Solver* solver = DimacsParser::parse(filename);
    auto end_parse = std::chrono::high_resolution_clock::now();

    if (!solver) {
        std::cerr << "c Parsing failed.\n";
        return 1;
    }

    std::chrono::duration<double> parse_time = end_parse - start_parse;
    std::cout << "c Parsed in " << parse_time.count() << " seconds.\n";
    std::cout << "c Variables: " << solver->values.size() / 2 << "\n";
    std::cout << "c Solving...\n";

    auto start_solve = std::chrono::high_resolution_clock::now();
    bool is_sat = solver->solve();
    auto end_solve = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double> solve_time = end_solve - start_solve;

    std::cout << "c Solved in " << solve_time.count() << " seconds.\n";

    if (is_sat) {
        std::cout << "s SATISFIABLE\n";
        std::cout << "v ";
        for (uint32_t i = 0; i < solver->values.size() / 2; i++) {
            Lit pos = make_literal(i, false);
            if (solver->values[pos] > 0) {
                std::cout << (i + 1) << " ";
            } else {
                std::cout << "-" << (i + 1) << " ";
            }
        }
        std::cout << "0\n";
    } else {
        std::cout << "s UNSATISFIABLE\n";
    }

    delete solver;
    return 0;
}