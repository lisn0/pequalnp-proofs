#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

constexpr int inputs = 14;
constexpr int samples = 1 << inputs;
constexpr int seedSize = 27;
using Word = std::uint64_t;
using Table = std::array<Word, samples / 64>;
enum class Op { And, Or };
struct Gate { Op op; int a; int b; };
using Circuit = std::vector<Gate>;

constexpr std::pair<int, int> edges[] = {
    {0, 7}, {0, 8}, {0, 10}, {1, 7}, {1, 9}, {1, 13}, {2, 8}, {2, 12}, {2, 13},
    {3, 7}, {3, 11}, {3, 12}, {4, 10}, {4, 11}, {4, 13}, {5, 9}, {5, 10}, {5, 12},
    {6, 8}, {6, 9}, {6, 11},
};

Circuit make_seed(int first, bool balanced) {
    Circuit out;
    auto add = [&](Op op, int a, int b) {
        int index = inputs + static_cast<int>(out.size());
        out.push_back({op, a, b});
        return index;
    };
    std::vector<int> terms;
    for (int v = first; v < first + 7; ++v) {
        std::vector<int> neighbors;
        for (auto [a, b] : edges) {
            if (v == a) neighbors.push_back(b);
            if (v == b) neighbors.push_back(a);
        }
        if (neighbors.size() != 3) throw std::runtime_error("expected degree three");
        int pair = add(Op::Or, neighbors[0], neighbors[1]);
        int sum = add(Op::Or, pair, neighbors[2]);
        terms.push_back(add(Op::And, v, sum));
    }
    if (balanced) {
        while (terms.size() > 1) {
            std::vector<int> next;
            std::size_t i = 0;
            for (; i + 1 < terms.size(); i += 2) {
                next.push_back(add(Op::Or, terms[i], terms[i + 1]));
            }
            if (i < terms.size()) next.push_back(terms[i]);
            terms = std::move(next);
        }
    } else {
        int sum = terms[0];
        for (std::size_t i = 1; i < terms.size(); ++i) sum = add(Op::Or, sum, terms[i]);
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
        std::array<Word, inputs + seedSize> wire{};
        std::array<bool, inputs + seedSize> matches{};
        matches.fill(true);
        for (std::size_t k = 0; k < target.size(); ++k) {
            for (int v = 0; v < inputs; ++v) wire[v] = input[v][k];
            bool any = false;
            for (std::size_t i = 0; i < gates.size(); ++i) {
                auto [op, a, b] = gates[i];
                Word next = op == Op::And ? wire[a] & wire[b] : wire[a] | wire[b];
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
        std::cout << (g.op == Op::And ? "and" : "or") << ' ' << g.a << ' ' << g.b << '\n';
    }
    std::cout << "output " << output << '\n';
}

int main() {
    const TruthTables tables;
    std::uint64_t checked = 0;
    auto check = [&](const Circuit& gates) {
        ++checked;
        int out = tables.matching_output(gates);
        if (out < 0) return false;
        print(gates, out);
        return true;
    };
    for (int variant = 0; variant < 4; ++variant) {
        Circuit seed = make_seed((variant / 2) * 7, variant % 2 == 0);
        if (seed.size() != seedSize || tables.matching_output(seed) != inputs + seedSize - 1) {
            throw std::runtime_error("seed does not compute the target with twenty-seven gates");
        }
        for (int skipped = 0; skipped < seedSize; ++skipped) {
            for (int substitute = 0; substitute < inputs + skipped; ++substitute) {
                Circuit trial = remove(seed, skipped, substitute);
                if (check(trial)) return 0;
                for (int j = 0; j < seedSize - 1; ++j) {
                    Gate previous = trial[j];
                    for (int a = 0; a < inputs + j; ++a) {
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
