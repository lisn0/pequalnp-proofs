#include <algorithm>
#include <array>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Clause = std::vector<int>;

constexpr int vertices = 6;
constexpr int assignments = 1 << vertices;

bool bit(int mask, int input) {
    return (mask & (1 << input)) != 0;
}

bool target(int mask, int output) {
    for (int left = 0; left < 3; ++left) {
        if (bit(mask, left) && bit(mask, 3 + (left + output) % 3)) {
            return true;
        }
    }
    return false;
}

struct Formula {
    int variables = 0;
    std::vector<Clause> clauses;

    int fresh() { return ++variables; }

    Clause oneOf(int count) {
        Clause choices;
        for (int i = 0; i < count; ++i) {
            choices.push_back(fresh());
            for (int j = 0; j < i; ++j) {
                clauses.push_back({-choices[i], -choices[j]});
            }
        }
        clauses.push_back(choices);
        return choices;
    }

    void print() const {
        std::cout << "p cnf " << variables << ' ' << clauses.size() << '\n';
        for (const auto& clause : clauses) {
            for (int literal : clause) {
                std::cout << literal << ' ';
            }
            std::cout << "0\n";
        }
    }
};

enum Op { And, Or, Not };

struct Selectors {
    Clause op;
    Clause left;
    Clause right;
};

struct Network {
    Formula f;
    std::vector<Selectors> gates;
    std::array<Clause, 3> outputs;

    explicit Network(int size) {
        for (int i = 0; i < size; ++i) {
            gates.push_back({f.oneOf(3), f.oneOf(vertices + i), f.oneOf(vertices + i)});
        }
        for (auto& output : outputs) {
            output = f.oneOf(size);
        }
    }

    void symmetry() {
        for (const auto& gate : gates) {
            f.clauses.push_back({-gate.op[Not], gate.right[0]});
            for (size_t i = 0; i < gate.left.size(); ++i) {
                for (size_t j = 0; j <= i; ++j) {
                    f.clauses.push_back({gate.op[Not], -gate.left[i], -gate.right[j]});
                }
            }
        }
        // Cycling the right-hand inputs and reversing both sides yields every output ordering.
        for (size_t k = 0; k + 1 < outputs.size(); ++k) {
            for (size_t i = 0; i < gates.size(); ++i) {
                for (size_t j = 0; j <= i; ++j) {
                    f.clauses.push_back({-outputs[k][i], -outputs[k + 1][j]});
                }
            }
        }
    }

    int read(const Clause& choices, const Clause& prior, int mask) {
        const int value = f.fresh();
        for (size_t i = 0; i < choices.size(); ++i) {
            const int select = choices[i];
            if (i < vertices) {
                f.clauses.push_back({-select, bit(mask, i) ? value : -value});
            } else {
                const int source = prior[i - vertices];
                f.clauses.push_back({-select, -source, value});
                f.clauses.push_back({-select, source, -value});
            }
        }
        return value;
    }

    void constrain(int mask) {
        Clause prior;
        for (const auto& gate : gates) {
            const int a = read(gate.left, prior, mask);
            const int b = read(gate.right, prior, mask);
            const int y = f.fresh();
            const int conj = gate.op[And];
            const int disj = gate.op[Or];
            const int neg = gate.op[Not];
            f.clauses.push_back({-conj, -y, a});
            f.clauses.push_back({-conj, -y, b});
            f.clauses.push_back({-conj, y, -a, -b});
            f.clauses.push_back({-disj, y, -a});
            f.clauses.push_back({-disj, y, -b});
            f.clauses.push_back({-disj, -y, a, b});
            f.clauses.push_back({-neg, -y, -a});
            f.clauses.push_back({-neg, y, a});
            prior.push_back(y);
        }
        for (size_t k = 0; k < outputs.size(); ++k) {
            const bool expected = target(mask, k);
            for (size_t i = 0; i < gates.size(); ++i) {
                f.clauses.push_back({-outputs[k][i], expected ? prior[i] : -prior[i]});
            }
        }
    }

    void fixControl() {
        if (gates.size() != 15) {
            throw std::runtime_error("the control has exactly 15 gates");
        }
        const auto fix = [this](int index, Op op, int left, int right) {
            f.clauses.push_back({gates[index].op[op]});
            f.clauses.push_back({gates[index].left[left]});
            f.clauses.push_back({gates[index].right[right]});
        };
        for (int k = 0; k < 3; ++k) {
            const int base = 5 * k;
            for (int left = 0; left < 3; ++left) {
                fix(base + left, And, left, 3 + (left + k) % 3);
            }
            fix(base + 3, Or, vertices + base, vertices + base + 1);
            fix(base + 4, Or, vertices + base + 2, vertices + base + 3);
            f.clauses.push_back({outputs[k][base + 4]});
        }
    }
};

struct Gate {
    Op op;
    int left;
    int right;
};

void decode(const Network& network) {
    std::vector<bool> model(network.f.variables + 1);
    bool sat = false;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line == "s SATISFIABLE") {
            sat = true;
        } else if (line.starts_with("v ")) {
            size_t offset = 2;
            while (offset < line.size()) {
                size_t length;
                const int literal = std::stoi(line.substr(offset), &length);
                offset += length;
                if (literal == 0) {
                    break;
                }
                if (literal > 0 && literal <= network.f.variables) {
                    model[literal] = true;
                }
            }
        }
    }
    if (!sat) {
        throw std::runtime_error("solver did not return a satisfying assignment");
    }
    const auto chosen = [&model](const Clause& choices) {
        for (int i = 0; i < static_cast<int>(choices.size()); ++i) {
            if (model[choices[i]]) {
                return i;
            }
        }
        throw std::runtime_error("missing choice in the solver assignment");
    };
    std::vector<Gate> gates;
    for (const auto& selectors : network.gates) {
        gates.push_back({
            static_cast<Op>(chosen(selectors.op)),
            chosen(selectors.left),
            chosen(selectors.right),
        });
    }
    std::array<int, 3> outputs;
    for (size_t k = 0; k < outputs.size(); ++k) {
        outputs[k] = vertices + chosen(network.outputs[k]);
    }
    for (int mask = 0; mask < assignments; ++mask) {
        std::vector<bool> wires;
        for (int i = 0; i < vertices; ++i) {
            wires.push_back(bit(mask, i));
        }
        for (const auto& gate : gates) {
            const bool a = wires[gate.left];
            const bool b = wires[gate.right];
            wires.push_back(gate.op == Not ? !a : gate.op == And ? a && b : a || b);
        }
        for (size_t k = 0; k < outputs.size(); ++k) {
            if (wires[outputs[k]] != target(mask, k)) {
                throw std::runtime_error("decoded circuit failed the full truth-table check");
            }
        }
    }
    std::cout << "Verified all " << assignments << " inputs for all three outputs.\n[";
    const char* separator = "";
    for (const auto& gate : gates) {
        const char* op = gate.op == Not ? "not" : gate.op == And ? "and" : "or";
        std::cout << separator << "⟨GateOp." << op << ", [" << gate.left;
        if (gate.op != Not) {
            std::cout << ", " << gate.right;
        }
        std::cout << "]⟩";
        separator = ",\n ";
    }
    std::cout << "]\nOutputs: " << outputs[0] << ", " << outputs[1] << ", " << outputs[2] << '\n';
}

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "Usage: search-meta-652 encode|control|decode GATE_COUNT\n";
        return 2;
    }
    const std::string mode = argv[1];
    const int count = std::stoi(argv[2]);
    if (count <= 0) {
        return 2;
    }
    Network network(count);
    if (mode == "decode") {
        decode(network);
    } else if (mode == "encode" || mode == "control") {
        network.symmetry();
        for (int mask = 0; mask < assignments; ++mask) {
            network.constrain(mask);
        }
        if (mode == "control") {
            network.fixControl();
        }
        network.f.print();
    } else {
        return 2;
    }
}
