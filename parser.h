#pragma once
#include <cmath>
#include <cstdio>
#include <iostream>
#include <string>
#include <vector>

#include "solver.h"

namespace CSat {

class DimacsParser {
   public:
    static Solver* parse(const std::string& filename) {
        FILE* file = fopen(filename.c_str(), "r");
        if (!file) {
            std::cerr << "Error: Could not open " << filename << "\n";
            return nullptr;
        }

        int vars = 0, clauses = 0;
        int ch;

        while ((ch = fgetc(file)) != EOF) {
            if (ch == 'c') {
                skip_line(file);
            } else if (ch == 'p') {
                for (int i = 0; i < 4; i++) fgetc(file);
                read_int(file, vars);
                read_int(file, clauses);
                break;
            } else {
                skip_line(file);
            }
        }

        if (vars == 0) {
            std::cerr << "Error: Invalid or missing 'p cnf' header.\n";
            fclose(file);
            return nullptr;
        }

        Solver* solver = new Solver(vars);
        std::vector<Lit> current_clause;

        int parsed_val;

        while (read_int(file, parsed_val)) {
            if (parsed_val == 0) {
                solver->add_original_clause(current_clause);
                current_clause.clear();
            } else {
                bool is_neg = (parsed_val < 0);
                uint32_t var = std::abs(parsed_val) - 1;

                if (var >= vars) {
                    std::cerr << "Parse error: Variable " << std::abs(parsed_val)
                              << " exceeds declared maximum (" << vars << ").\n";
                    delete solver;
                    return nullptr;
                }

                current_clause.push_back(make_literal(var, is_neg));
            }
        }

        fclose(file);
        return solver;
    }

   private:
    static void skip_line(FILE* file) {
        int ch;
        while ((ch = fgetc(file)) != '\n' && ch != EOF) {}
    }

    static bool read_int(FILE* file, int& out_val) {
        int ch = fgetc(file);

        while (true) {
            while (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') {
                ch = fgetc(file);
            }

            if (ch == 'c') {
                while (ch != '\n' && ch != EOF) {
                    ch = fgetc(file);
                }
            } else {
                break;
            }
        }

        if (ch == EOF) return false;

        if (ch == '%') return false;

        if (ch != '-' && (ch < '0' || ch > '9')) {
            std::cerr << "Parse error: unexpected character '" << (char)ch << "' in file.\n";
            return false;
        }

        int sign = 1;
        if (ch == '-') {
            sign = -1;
            ch = fgetc(file);

            if (ch < '0' || ch > '9') {
                std::cerr << "Parse error: expected digit after '-'\n";
                return false;
            }
        }

        int val = 0;
        while (ch >= '0' && ch <= '9') {
            val = val * 10 + (ch - '0');
            ch = fgetc(file);
        }

        if (ch != EOF) ungetc(ch, file);

        out_val = sign * val;
        return true;
    }
};
}  // namespace CSat