#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Wire = std::uint16_t;
using Coverage = std::uint64_t;
constexpr int inputs = 6;
constexpr int budget = 9;
constexpr std::array<int, 9> edges{3, 5, 6, 24, 40, 48, 9, 18, 36};

int main() {
    auto independent = [](int mask) {
        return std::none_of(edges.begin(), edges.end(), [=](int edge) { return (mask & edge) == edge; });
    };
    std::vector<int> examples;
    for (int mask = 0; mask < (1 << inputs); ++mask) {
        if (!independent(mask)) continue;
        bool maximal = true;
        for (int v = 0; v < inputs; ++v) {
            if ((mask & (1 << v)) == 0 && independent(mask | (1 << v))) maximal = false;
        }
        if (maximal) examples.push_back(mask);
    }
    if (examples.size() != 6) throw std::runtime_error("expected six maximal independent sets");
    examples.insert(examples.end(), edges.begin(), edges.end());
    constexpr int negatives = 6;
    const Wire goal = ((1 << edges.size()) - 1) << negatives;
    const Coverage full = (Coverage{1} << (negatives * edges.size())) - 1;
    std::vector<Coverage> separates(1 << examples.size());
    for (unsigned w = 0; w < separates.size(); ++w) {
        for (int p = 0; p < static_cast<int>(edges.size()); ++p) {
            for (int n = 0; n < negatives; ++n) {
                if ((w >> (negatives + p) & 1u) && !(w >> n & 1u)) {
                    separates[w] |= Coverage{1} << (p * negatives + n);
                }
            }
        }
    }
    std::vector<Wire> start(inputs);
    for (int v = 0; v < inputs; ++v) {
        for (std::size_t i = 0; i < examples.size(); ++i) {
            if (examples[i] & (1 << v)) start[v] |= 1 << i;
        }
        std::cout << "input " << v << " signature " << start[v] << '\n';
    }
    std::array<std::unordered_set<std::string>, budget + 1> explored;
    std::uint64_t visited = 0;
    auto search = [&](auto&& self, int left, std::vector<Wire> wires) -> bool {
        if (wires.size() == 1 && wires.front() == goal) return true;
        if (left == 0) return false;
        std::sort(wires.begin(), wires.end());
        std::string key(reinterpret_cast<const char*>(wires.data()), wires.size() * sizeof(Wire));
        if (!explored[left].insert(std::move(key)).second) return false;
        ++visited;
        for (std::size_t a = 0; a < wires.size(); ++a) {
            for (std::size_t b = a + 1; b < wires.size(); ++b) {
                Wire x = wires[a], y = wires[b];
                std::array<Wire, 2> outputs{Wire(x & y), Wire(x | y)};
                for (int op = 0; op < 2; ++op) {
                    Wire out = outputs[op];
                    if (std::binary_search(wires.begin(), wires.end(), out)) continue;
                    for (unsigned keep = 0; keep < 4; ++keep) {
                        if (wires.size() - 1 + std::popcount(keep) > static_cast<unsigned>(left)) continue;
                        Coverage coverage = separates[out];
                        std::vector<Wire> next{out};
                        for (std::size_t i = 0; i < wires.size(); ++i) {
                            if ((i == a && !(keep & 1)) || (i == b && !(keep & 2))) continue;
                            coverage |= separates[wires[i]];
                            next.push_back(wires[i]);
                        }
                        if (coverage == full && self(self, left - 1, std::move(next))) {
                            std::cout << x << (op == 0 ? " AND " : " OR ") << y << " = " << out << '\n';
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    };
    bool found = search(search, budget, start);
    std::cout << (found ? "Witness" : "No witness") << " after " << visited << " distinct frontiers\n";
}
