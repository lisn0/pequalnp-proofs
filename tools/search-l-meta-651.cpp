#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <regex>
#include <stdexcept>
#include <utility>
#include <vector>

constexpr int inputs = 10;
constexpr int samples = 1 << inputs;
using Word = std::uint64_t;
using Table = std::array<Word, samples / 64>;
enum class Op { And, Or, Not };
struct Gate { Op op; int a; int b; };
using Circuit = std::vector<Gate>;

constexpr std::pair<int, int> edges[] = {
    {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {0, 5}, {1, 6}, {2, 7},
    {3, 8}, {4, 9}, {5, 7}, {7, 9}, {9, 6}, {6, 8}, {8, 5},
};

Circuit read_seed(const char* path) {
    std::ifstream file(path);
    if (!file) throw std::runtime_error("cannot read the seed proof");
    std::string text((std::istreambuf_iterator<char>(file)), {});
    std::regex gate(R"(GateOp\.(and|or),\s*\[(\d+),\s*(\d+)\])");
    Circuit out;
    for (std::sregex_iterator it(text.begin(), text.end(), gate), end; it != end; ++it) {
        int a = std::stoi((*it)[2]);
        int b = std::stoi((*it)[3]);
        if (a >= inputs + static_cast<int>(out.size()) || b >= inputs + static_cast<int>(out.size())) {
            throw std::runtime_error("seed is not topologically ordered");
        }
        out.push_back({(*it)[1] == "and" ? Op::And : Op::Or, a, b});
    }
    if (out.size() != 20 || text.find("output := 29") == std::string::npos) {
        throw std::runtime_error("expected a twenty-gate seed with its last wire as output");
    }
    return out;
}

struct TruthTables {
    std::array<Table, inputs> input{};
    Table target{};

    TruthTables() {
        std::array<bool, samples> positive{};
        std::array<bool, samples> selected{};
        std::vector<int> ordered;
        auto add = [&](int mask) {
            if (!selected[mask]) ordered.push_back(mask);
            selected[mask] = true;
        };
        for (auto [a, b] : edges) {
            int edge = (1 << a) | (1 << b);
            add(edge);
            for (int mask = 0; mask < samples; ++mask) {
                positive[mask] = positive[mask] || (mask & edge) == edge;
            }
        }
        for (int mask = 0; mask < samples; ++mask) {
            if (positive[mask]) continue;
            bool maximal = true;
            for (int v = 0; v < inputs; ++v) {
                if ((mask & (1 << v)) == 0 && !positive[mask | (1 << v)]) maximal = false;
            }
            if (maximal) add(mask);
        }
        for (int mask = 0; mask < samples; ++mask) add(mask);
        for (int i = 0; i < samples; ++i) {
            Word bit = Word{1} << (i % 64);
            int mask = ordered[i];
            if (positive[mask]) target[i / 64] |= bit;
            for (int v = 0; v < inputs; ++v) {
                if (mask & (1 << v)) input[v][i / 64] |= bit;
            }
        }
    }

    int matching_output(const Circuit& gates) const {
        std::array<Word, inputs + 20> wire{};
        std::array<bool, inputs + 20> matches{};
        matches.fill(true);
        for (std::size_t k = 0; k < target.size(); ++k) {
            for (int v = 0; v < inputs; ++v) wire[v] = input[v][k];
            bool any = false;
            for (std::size_t i = 0; i < gates.size(); ++i) {
                auto [op, a, b] = gates[i];
                Word next = op == Op::And ? wire[a] & wire[b] :
                    op == Op::Or ? wire[a] | wire[b] : ~wire[a];
                wire[inputs + i] = next;
                matches[inputs + i] = matches[inputs + i] && next == target[k];
                any = any || matches[inputs + i];
            }
            if (!any) return -1;
        }
        for (std::size_t i = 0; i < gates.size(); ++i) {
            if (matches[inputs + i]) return inputs + static_cast<int>(i);
        }
        return -1;
    }
};

Circuit remove(const Circuit& seed, int skipped, int substitute) {
    Circuit out;
    auto remap = [&](int wire) {
        if (wire == inputs + skipped) return substitute;
        return wire - (wire > inputs + skipped ? 1 : 0);
    };
    for (int j = 0; j < static_cast<int>(seed.size()); ++j) {
        if (j == skipped) continue;
        const auto& g = seed[j];
        out.push_back({g.op, remap(g.a), remap(g.b)});
    }
    return out;
}

void print(const Circuit& gates, int output) {
    for (const auto& g : gates) {
        std::cout << (g.op == Op::And ? "and" : g.op == Op::Or ? "or" : "not") << ' ' << g.a;
        if (g.op != Op::Not) std::cout << ' ' << g.b;
        std::cout << '\n';
    }
    std::cout << "output " << output << '\n';
}

int main(int argc, char** argv) {
    const TruthTables tables;
    std::uint64_t checked = 0;
    auto check = [&](const Circuit& gates) {
        ++checked;
        int out = tables.matching_output(gates);
        if (out < 0) return false;
        print(gates, out);
        return true;
    };
    if (argc < 2) throw std::runtime_error("provide one or more twenty-gate seed proof files");
    for (int arg = 1; arg < argc; ++arg) {
        Circuit seed = read_seed(argv[arg]);
        if (tables.matching_output(seed) != 29) throw std::runtime_error("seed does not compute the target");
        for (int skipped = 0; skipped < 20; ++skipped) {
            for (int substitute = 0; substitute < inputs + skipped; ++substitute) {
                Circuit trial = remove(seed, skipped, substitute);
                if (check(trial)) return 0;
                for (int j = 0; j < 19; ++j) {
                    Gate previous = trial[j];
                    for (int a = 0; a < inputs + j; ++a) {
                        trial[j] = {Op::Not, a, a};
                        if (check(trial)) return 0;
                        for (int b = a; b < inputs + j; ++b) {
                            trial[j] = {Op::And, a, b};
                            if (check(trial)) return 0;
                            trial[j] = {Op::Or, a, b};
                            if (check(trial)) return 0;
                        }
                    }
                    trial[j] = previous;
                }
            }
        }
    }
    std::cout << "No witness among " << checked << " tested circuits\n";
}
