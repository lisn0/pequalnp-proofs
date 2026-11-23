#include <array>
#include <initializer_list>
#include <iostream>
#include <set>
#include <string_view>
#include <utility>
#include <vector>

constexpr int vertices = 10;
constexpr int gates = 5;

struct Formula {
    int variables = 0;
    std::vector<std::vector<int>> clauses;

    int fresh() { return ++variables; }

    int either(std::vector<int> terms) {
        int output = fresh();
        for (int term : terms) {
            clauses.push_back({-term, output});
        }
        terms.push_back(-output);
        clauses.push_back(std::move(terms));
        return output;
    }

    int both(int left, int right) {
        int output = fresh();
        clauses.push_back({-output, left});
        clauses.push_back({-output, right});
        clauses.push_back({output, -left, -right});
        return output;
    }
};

bool contains(int mask, int v) { return (mask & (1 << v)) != 0; }

int main(int argc, char** argv) {
    constexpr std::pair<int, int> edges[] = {
        {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {0, 5}, {1, 6}, {2, 7},
        {3, 8}, {4, 9}, {5, 7}, {6, 8}, {7, 9}, {8, 5}, {9, 6},
    };
    std::array<bool, 1 << vertices> independent{};
    for (int mask = 0; mask < (1 << vertices); ++mask) {
        independent[mask] = true;
        for (auto [a, b] : edges) {
            if (contains(mask, a) && contains(mask, b)) {
                independent[mask] = false;
                break;
            }
        }
    }

    std::set<int> negatives;
    std::set<int> positives;
    for (int mask = 0; mask < (1 << vertices); ++mask) {
        if (!independent[mask]) {
            continue;
        }
        std::vector<int> extensions;
        bool maximal = true;
        for (int v = 0; v < vertices; ++v) {
            if (!contains(mask, v)) {
                int extension = mask | (1 << v);
                maximal = maximal && !independent[extension];
                extensions.push_back(extension);
            }
        }
        if (maximal) {
            negatives.insert(mask);
            positives.insert(extensions.begin(), extensions.end());
        }
    }

    Formula cnf;
    int bare[gates][2][vertices];
    int wire[gates][2][gates];
    int output[gates];
    for (int i = 0; i < gates; ++i) {
        for (int side = 0; side < 2; ++side) {
            for (int v = 0; v < vertices; ++v) {
                bare[i][side][v] = cnf.fresh();
            }
            for (int j = 0; j < i; ++j) {
                wire[i][side][j] = cnf.fresh();
            }
        }
        output[i] = cnf.fresh();
    }

    if (argc == 2 && std::string_view(argv[1]) == "--normalized") {
        for (int v = 0; v < vertices; ++v) {
            std::vector<int> occurrences;
            for (int i = 0; i < gates; ++i) {
                occurrences.push_back(bare[i][0][v]);
                occurrences.push_back(bare[i][1][v]);
                cnf.clauses.push_back({-bare[i][0][v], -bare[i][1][v]});
            }
            cnf.clauses.push_back(occurrences);
            for (int a = 0; a < 2 * gates; ++a) {
                for (int b = a + 1; b < 2 * gates; ++b) {
                    for (int c = b + 1; c < 2 * gates; ++c) {
                        cnf.clauses.push_back({-occurrences[a], -occurrences[b], -occurrences[c]});
                    }
                }
            }
        }
    }

    auto circuit = [&](int mask) {
        int value[gates];
        std::vector<int> outputTerms;
        for (int i = 0; i < gates; ++i) {
            int sides[2];
            for (int side = 0; side < 2; ++side) {
                std::vector<int> terms;
                for (int v = 0; v < vertices; ++v) {
                    if (contains(mask, v)) {
                        terms.push_back(bare[i][side][v]);
                    }
                }
                for (int j = 0; j < i; ++j) {
                    terms.push_back(cnf.both(wire[i][side][j], value[j]));
                }
                sides[side] = cnf.either(std::move(terms));
            }
            value[i] = cnf.both(sides[0], sides[1]);
            outputTerms.push_back(cnf.both(output[i], value[i]));
        }
        return cnf.either(std::move(outputTerms));
    };

    for (int mask : negatives) {
        cnf.clauses.push_back({-circuit(mask)});
    }
    for (int mask : positives) {
        cnf.clauses.push_back({circuit(mask)});
    }

    std::cerr << negatives.size() << " negative and " << positives.size() << " positive inputs\n";
    std::cout << "p cnf " << cnf.variables << ' ' << cnf.clauses.size() << '\n';
    for (const auto& clause : cnf.clauses) {
        for (int literal : clause) {
            std::cout << literal << ' ';
        }
        std::cout << "0\n";
    }
}
