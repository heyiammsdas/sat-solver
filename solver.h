#pragma once
#include <cassert>
#include <cstdint>
#include <vector>
#include <cstddef> // #1

namespace CSat {

typedef uint32_t Lit;

inline Lit make_literal(uint32_t var, bool is_negative) {
    return (var << 1) | (is_negative ? 1 : 0);
}

inline uint32_t get_var(Lit lit) { return lit >> 1; }

inline bool is_negative(Lit lit) { return lit & 1; }

inline Lit negate_lit(Lit lit) { return lit ^ 1; }

typedef uint32_t ClauseRef;
const ClauseRef CLAUSE_REF_NULL = 0xFFFFFFFF;

class ClauseArena {
   private:
    std::vector<uint32_t> memory;

   public:
    ClauseArena() { memory.push_back(0); }

    size_t get_memory_size() const { return memory.size(); }

    ClauseRef add_clause(const std::vector<Lit>& literals) {
        ClauseRef offset = memory.size();

        memory.push_back(literals.size());

        for (Lit l : literals) {
            memory.push_back(l);
        }

        return offset;
    }

    Lit* get_literals(ClauseRef ref) {
        assert(ref < memory.size());

        return &memory[ref + 1];
    }

    uint32_t get_size(ClauseRef ref) {
        assert(ref < memory.size());
        return memory[ref];
    }
};

struct Watch {
    Lit blocking_literal;
    uint32_t data : 31;
    uint32_t is_binary : 1;

    static Watch make_binary(Lit blocking, Lit other) {
        Watch w;
        w.blocking_literal = blocking;
        w.data = other;
        w.is_binary = 1;
        return w;
    }

    static Watch make_large(Lit blocking, ClauseRef offset) {
        Watch w;
        w.blocking_literal = blocking;
        w.data = offset;
        w.is_binary = 0;
        return w;
    }
};

static_assert(sizeof(Watch) == 8, "Watch struct must be exactly 8 bytes!");

class Solver {
   public:
    ClauseArena arena;

    std::vector<std::vector<Watch>> watches;
    std::vector<int8_t> values;
    std::vector<Lit> trail;
    std::vector<int> level;
    std::vector<ClauseRef> reason;
    std::vector<uint8_t> seen;
    int decision_level;
    std::vector<int> trail_lim;
    std::vector<double> activity;
    double var_inc;
    std::vector<uint32_t> heap;
    std::vector<int> indices;
    std::vector<int8_t> saved_phase;

    int qhead;

    static const ClauseRef CLAUSE_REF_UNDEF = 0xFFFFFFFF;
    static const ClauseRef CLAUSE_REF_BINARY_CONFLICT = 0xFFFFFFFE;

    inline ClauseRef pack_binary_reason(Lit lit) { return 0x80000000 | lit; }
    inline bool is_binary_reason(ClauseRef cr) {
        return (cr & 0x80000000) != 0 && cr != CLAUSE_REF_UNDEF && cr != CLAUSE_REF_BINARY_CONFLICT;
    }
    inline Lit unpack_binary_reason(ClauseRef cr) { return cr & 0x7FFFFFFF; }

    Lit conflict_binary_lit1;
    Lit conflict_binary_lit2;

    bool is_unsat;

    Solver(int num_vars) {
        watches.resize(num_vars * 2);
        values.resize(num_vars * 2, 0);

        level.resize(num_vars, 0);
        reason.resize(num_vars, CLAUSE_REF_UNDEF);
        seen.resize(num_vars, 0);

        activity.resize(num_vars, 0.0);
        indices.resize(num_vars, -1);
        var_inc = 1.0;
        saved_phase.resize(num_vars, 1);

        for (int i = 0; i < num_vars; i++) {
            insert_var_order(i);
        }

        qhead = 0;
        decision_level = 0;
        is_unsat = false;
    }

    void unchecked_enqueue(Lit p, ClauseRef from = CLAUSE_REF_UNDEF) {
        if (values[p] != 0) return;

        values[p] = 1;
        values[negate_lit(p)] = -1;

        uint32_t var = get_var(p);
        level[var] = decision_level;
        reason[var] = from;

        saved_phase[var] = is_negative(p);

        trail.push_back(p);
    }

    void add_original_clause(std::vector<Lit>& literals) {
        if (is_unsat) return;

        if (literals.size() == 0) {
            is_unsat = true;
        } else if (literals.size() == 1) {
            Lit p = literals[0];
            if (values[p] == 0) {
                unchecked_enqueue(p);
            } else if (values[p] < 0) {
                is_unsat = true;
            }
        } else if (literals.size() == 2) {
            Lit l0 = literals[0];
            Lit l1 = literals[1];

            watches[l0].push_back(Watch::make_binary(l1, l1));

            watches[l1].push_back(Watch::make_binary(l0, l0));
        } else {
            ClauseRef ref = arena.add_clause(literals);

            Lit l0 = literals[0];
            Lit l1 = literals[1];

            watches[l0].push_back(Watch::make_large(l1, ref));

            watches[l1].push_back(Watch::make_large(l0, ref));
        }
    }

    ClauseRef propagate() {
        ClauseRef conflict = CLAUSE_REF_UNDEF;

        while (qhead < trail.size()) {
            Lit p = trail[qhead++];
            Lit false_lit = negate_lit(p);

            std::vector<Watch>& ws = watches[false_lit];

            size_t i = 0;
            size_t j = 0;

            while (i < ws.size()) {
                Watch w = ws[i];

                if (values[w.blocking_literal] > 0) {
                    ws[j++] = ws[i++];
                    continue;
                }

                if (w.is_binary) {
                    Lit other = w.data;

                    if (values[other] < 0) {
                        conflict = CLAUSE_REF_BINARY_CONFLICT;
                        conflict_binary_lit1 = false_lit;
                        conflict_binary_lit2 = other;

                        while (i < ws.size()) ws[j++] = ws[i++];
                        break;
                    } else if (values[other] == 0) {
                        unchecked_enqueue(other, pack_binary_reason(false_lit));
                    }
                    ws[j++] = ws[i++];
                }

                else {
                    ClauseRef cr = w.data;
                    Lit* lits = arena.get_literals(cr);
                    uint32_t size = arena.get_size(cr);

                    if (lits[0] == false_lit) {
                        lits[0] = lits[1];
                        lits[1] = false_lit;
                    }

                    Lit first_lit = lits[0];

                    if (values[first_lit] > 0) {
                        ws[i].blocking_literal = first_lit;
                        ws[j++] = ws[i++];
                        continue;
                    }

                    bool found_new_watch = false;

                    for (uint32_t k = 2; k < size; k++) {
                        if (values[lits[k]] >= 0) {
                            lits[1] = lits[k];
                            lits[k] = false_lit;

                            watches[lits[1]].push_back(Watch::make_large(lits[0], cr));

                            found_new_watch = true;
                            break;
                        }
                    }

                    if (found_new_watch) {
                        i++;
                    } else {
                        if (values[first_lit] < 0) {
                            conflict = cr;

                            while (i < ws.size()) ws[j++] = ws[i++];
                            break;
                        } else {
                            unchecked_enqueue(first_lit, cr);

                            ws[i].blocking_literal = first_lit;
                            ws[j++] = ws[i++];
                        }
                    }
                }
            }

            ws.resize(j);

            if (conflict != CLAUSE_REF_UNDEF) {
                return conflict;
            }
        }

        return CLAUSE_REF_UNDEF;
    }

    int analyze(ClauseRef conflict, std::vector<Lit>& out_learned) {
        int pathC = 0;
        Lit p = 0;
        int index = trail.size() - 1;

        out_learned.push_back(0);

        do {
            Lit bin_lits[2];
            Lit* lits;
            uint32_t size;

            if (conflict == CLAUSE_REF_BINARY_CONFLICT) {
                bin_lits[0] = conflict_binary_lit1;
                bin_lits[1] = conflict_binary_lit2;
                lits = bin_lits;
                size = 2;
            } else if (is_binary_reason(conflict)) {
                bin_lits[0] = p;
                bin_lits[1] = unpack_binary_reason(conflict);
                lits = bin_lits;
                size = 2;
            } else {
                lits = arena.get_literals(conflict);
                size = arena.get_size(conflict);
            }

            for (uint32_t j = (p == 0 ? 0 : 1); j < size; j++) {
                Lit q = lits[j];
                uint32_t var = get_var(q);

                if (!seen[var] && level[var] > 0) {
                    seen[var] = 1;

                    if (level[var] >= decision_level) {
                        pathC++;
                    } else {
                        out_learned.push_back(q);
                    }
                }
            }

            while (!seen[get_var(trail[index])]) {
                index--;
            }

            p = trail[index];
            conflict = reason[get_var(p)];
            seen[get_var(p)] = 0;
            pathC--;
            index--;

        } while (pathC > 0);

        out_learned[0] = negate_lit(p);

        for (Lit l : out_learned) {
            seen[get_var(l)] = 0;
        }

        if (out_learned.size() == 1) {
            return 0;
        } else {
            int max_idx = 1;
            int max_lvl = level[get_var(out_learned[1])];

            for (size_t i = 2; i < out_learned.size(); i++) {
                if (level[get_var(out_learned[i])] > max_lvl) {
                    max_lvl = level[get_var(out_learned[i])];
                    max_idx = i;
                }
            }

            Lit tmp = out_learned[1];
            out_learned[1] = out_learned[max_idx];
            out_learned[max_idx] = tmp;

            return max_lvl;
        }
    }

    void cancel_until(int target_level) {
        if (decision_level <= target_level) {
            return;
        }

        int target_trail_size = trail_lim[target_level];

        for (int c = trail.size() - 1; c >= target_trail_size; c--) {
            Lit p = trail[c];
            values[p] = 0;
            values[negate_lit(p)] = 0;
            insert_var_order(get_var(p));
        }

        qhead = target_trail_size;

        trail.resize(target_trail_size);
        trail_lim.resize(target_level);

        decision_level = target_level;
    }

    inline int left_child(int i) { return i * 2 + 1; }
    inline int right_child(int i) { return i * 2 + 2; }
    inline int parent(int i) { return (i - 1) / 2; }

    void heap_sift_up(int i) {
        uint32_t x = heap[i];
        int p = parent(i);
        while (i > 0 && activity[x] > activity[heap[p]]) {
            heap[i] = heap[p];
            indices[heap[i]] = i;
            i = p;
            p = parent(p);
        }
        heap[i] = x;
        indices[x] = i;
    }

    void heap_sift_down(int i) {
        uint32_t x = heap[i];
        while (left_child(i) < heap.size()) {
            int child = left_child(i);
            if (child + 1 < heap.size() && activity[heap[child + 1]] > activity[heap[child]]) {
                child++;
            }
            if (activity[x] >= activity[heap[child]]) break;

            heap[i] = heap[child];
            indices[heap[i]] = i;
            i = child;
        }
        heap[i] = x;
        indices[x] = i;
    }

    void insert_var_order(uint32_t var) {
        if (indices[var] == -1) {
            indices[var] = heap.size();
            heap.push_back(var);
            heap_sift_up(indices[var]);
        }
    }

    uint32_t pop_highest_activity_var() {
        uint32_t max_var = heap[0];
        heap[0] = heap.back();
        indices[heap[0]] = 0;
        indices[max_var] = -1;
        heap.pop_back();

        if (!heap.empty()) {
            heap_sift_down(0);
        }
        return max_var;
    }

    void var_decay_activity() { var_inc *= (1.0 / 0.95); }

    void var_bump_activity(uint32_t var) {
        activity[var] += var_inc;

        if (indices[var] != -1) {
            heap_sift_up(indices[var]);
        }

        if (activity[var] > 1e100) {
            for (size_t i = 0; i < activity.size(); i++) {
                activity[i] *= 1e-100;
            }
            var_inc *= 1e-100;
        }
    }

    Lit pick_branch_lit() {
        uint32_t next = 0xFFFFFFFF;

        while (!heap.empty()) {
            next = pop_highest_activity_var();

            if (values[make_literal(next, false)] == 0) {
                break;
            }
        }

        if (next == 0xFFFFFFFF || values[make_literal(next, false)] != 0) {
            return 0xFFFFFFFF;
        }

        bool sign = saved_phase[next];

        return make_literal(next, sign);
    }

    bool solve() {
        if (is_unsat) return false;

        if (propagate() != CLAUSE_REF_UNDEF) {
            return false;
        }

        std::vector<Lit> learned_clause;

        while (true) {
            ClauseRef conflict = propagate();

            if (conflict != CLAUSE_REF_UNDEF) {
                if (decision_level == 0) {
                    return false;
                }

                learned_clause.clear();

                int backtrack_level = analyze(conflict, learned_clause);

                for (Lit l : learned_clause) {
                    var_bump_activity(get_var(l));
                }

                cancel_until(backtrack_level);

                if (learned_clause.size() == 1) {
                    unchecked_enqueue(learned_clause[0]);
                } else {
                    ClauseRef cr = arena.add_clause(learned_clause);

                    Lit l0 = learned_clause[0];
                    Lit l1 = learned_clause[1];

                    watches[l0].push_back(Watch::make_large(l1, cr));
                    watches[l1].push_back(Watch::make_large(l0, cr));

                    unchecked_enqueue(l0, cr);
                }

                var_decay_activity();

            } else {
                Lit next_decision = pick_branch_lit();

                if (next_decision == 0xFFFFFFFF) {
                    return true;
                }

                decision_level++;
                trail_lim.push_back(trail.size());
                unchecked_enqueue(next_decision);
            }
        }
    }
};

}  // namespace CSat