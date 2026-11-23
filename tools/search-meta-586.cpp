#include <algorithm>
#include <array>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Clause = std::vector<int>;
using Bits = std::vector<bool>;

constexpr int inputCount = 8;
constexpr std::array<std::pair<int, int>, 9> edges{{
    {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {1, 5}, {5, 6}, {6, 7}, {7, 0},
}};

bool input(int mask, int vertex) {
    return (mask & (1 << vertex)) != 0;
}

bool target(int mask) {
    return std::any_of(edges.begin(), edges.end(), [mask](auto edge) {
        return input(mask, edge.first) && input(mask, edge.second);
    });
}

struct Formula {
    int variables = 0;
    std::vector<Clause> clauses;

    int variable() { return ++variables; }

    Clause variablesFor(int count) {
        Clause result;
        for (int i = 0; i < count; ++i) {
            result.push_back(variable());
        }
        return result;
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

struct Network {
    Formula formula;
    std::vector<std::array<Clause, 2>> operands;
    Clause output;

    explicit Network(int orCount) {
        for (int i = 0; i < orCount; ++i) {
            operands.push_back({
                formula.variablesFor(inputCount + i),
                formula.variablesFor(inputCount + i),
            });
        }
        output = formula.variablesFor(inputCount + orCount);
    }

    int conjunction(const Clause& selected, const Clause& previous, int mask) {
        Clause falseFactors;
        for (int i = 0; i < inputCount; ++i) {
            if (!input(mask, i)) {
                falseFactors.push_back(selected[i]);
            }
        }
        for (int i = 0; i < static_cast<int>(previous.size()); ++i) {
            const int choice = selected[inputCount + i];
            const int value = previous[i];
            const int bad = formula.variable();
            formula.clauses.push_back({-bad, choice});
            formula.clauses.push_back({-bad, -value});
            formula.clauses.push_back({bad, -choice, value});
            falseFactors.push_back(bad);
        }
        const int result = formula.variable();
        for (int bad : falseFactors) {
            formula.clauses.push_back({-result, -bad});
        }
        falseFactors.push_back(result);
        formula.clauses.push_back(std::move(falseFactors));
        return result;
    }

    void constrain(int mask, bool expected) {
        Clause previous;
        for (const auto& [left, right] : operands) {
            const int a = conjunction(left, previous, mask);
            const int b = conjunction(right, previous, mask);
            const int out = formula.variable();
            formula.clauses.push_back({-a, out});
            formula.clauses.push_back({-b, out});
            formula.clauses.push_back({-out, a, b});
            previous.push_back(out);
        }
        const int value = conjunction(output, previous, mask);
        formula.clauses.push_back({expected ? value : -value});
    }
};

bool maximalIndependent(int mask) {
    if (target(mask)) {
        return false;
    }
    for (int i = 0; i < inputCount; ++i) {
        if (!input(mask, i) && !target(mask | (1 << i))) {
            return false;
        }
    }
    return true;
}

void emit(Network& network) {
    for (auto [a, b] : edges) {
        network.constrain((1 << a) | (1 << b), true);
    }
    for (int mask = 0; mask < (1 << inputCount); ++mask) {
        if (maximalIndependent(mask)) {
            network.constrain(mask, false);
        }
    }
    network.formula.print();
}

struct Gate {
    bool isOr;
    Clause inputs;
};

struct Circuit {
    std::vector<Gate> gates;

    int add(bool isOr, Clause inputs) {
        gates.push_back({isOr, std::move(inputs)});
        return inputCount + static_cast<int>(gates.size()) - 1;
    }

    int conjunction(const Clause& selected, const Clause& wires, const Bits& model) {
        Clause factors;
        for (size_t i = 0; i < selected.size(); ++i) {
            if (model[selected[i]]) {
                factors.push_back(wires[i]);
            }
        }
        if (factors.empty()) {
            return add(false, {});
        }
        int value = factors.front();
        for (size_t i = 1; i < factors.size(); ++i) {
            value = add(false, {value, factors[i]});
        }
        return value;
    }

    bool evaluate(int mask, int output) const {
        Bits values;
        for (int vertex = 0; vertex < inputCount; ++vertex) {
            values.push_back(input(mask, vertex));
        }
        for (const auto& gate : gates) {
            const auto isTrue = [&values](int i) { return bool(values[i]); };
            const bool value = gate.isOr
                ? std::any_of(gate.inputs.begin(), gate.inputs.end(), isTrue)
                : std::all_of(gate.inputs.begin(), gate.inputs.end(), isTrue);
            values.push_back(value);
        }
        return values[output];
    }
};

void decode(const Network& network) {
    Bits model(network.formula.variables + 1);
    bool satisfiable = false;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line == "s SATISFIABLE") {
            satisfiable = true;
        } else if (line.starts_with("v ")) {
            size_t offset = 2;
            while (offset < line.size()) {
                size_t length;
                const int literal = std::stoi(line.substr(offset), &length);
                offset += length;
                if (literal == 0) {
                    break;
                }
                if (literal > 0 && literal <= network.formula.variables) {
                    model[literal] = true;
                }
            }
        }
    }
    if (!satisfiable) {
        throw std::runtime_error("solver did not return a satisfying assignment");
    }

    Circuit circuit;
    Clause wires;
    for (int i = 0; i < inputCount; ++i) {
        wires.push_back(i);
    }
    for (const auto& [left, right] : network.operands) {
        const int a = circuit.conjunction(left, wires, model);
        const int b = circuit.conjunction(right, wires, model);
        wires.push_back(circuit.add(true, {a, b}));
    }
    const int output = circuit.conjunction(network.output, wires, model);
    for (int mask = 0; mask < (1 << inputCount); ++mask) {
        if (circuit.evaluate(mask, output) != target(mask)) {
            throw std::runtime_error("decoded circuit fails truth-table evaluation");
        }
    }

    std::cout << "Verified all " << (1 << inputCount) << " inputs.\n";
    std::cout << "Gates:\n[";
    const char* separator = "";
    for (const auto& gate : circuit.gates) {
        std::cout << separator << "⟨GateOp." << (gate.isOr ? "or" : "and") << ", [";
        const char* comma = "";
        for (int index : gate.inputs) {
            std::cout << comma << index;
            comma = ", ";
        }
        std::cout << "]⟩";
        separator = ",\n ";
    }
    std::cout << "]\nOutput index: " << output << '\n';
}

int main(int argc, char** argv) {
    if (argc != 3 || (std::string(argv[1]) != "encode" && std::string(argv[1]) != "decode")) {
        std::cerr << "Usage: search-meta-586 encode|decode OR_COUNT\n";
        return 2;
    }
    Network network(std::stoi(argv[2]));
    if (std::string(argv[1]) == "encode") {
        emit(network);
    } else {
        decode(network);
    }
}
