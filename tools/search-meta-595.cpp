#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <string_view>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using Table = unsigned __int128;
using Probes = std::array<std::uint64_t, 10>;
constexpr int inputCount = 7;
constexpr int budget = 10;
constexpr int maxBudget = 11;
constexpr std::size_t cacheLimit = 180'000;
constexpr std::array<std::pair<int, int>, 8> edges{{
    {0, 1}, {0, 2}, {2, 1}, {0, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 1},
}};

struct Gate {
    char op;
    int a;
    int b;
};

struct Wire {
    Table value;
    Probes distinguishes;
    int index;
};

struct State {
    std::array<Table, maxBudget + 1> values{};
    int remaining;
    bool operator==(const State&) const = default;
};

std::size_t hashTable(Table value) {
    std::uint64_t hash = static_cast<std::uint64_t>(value) ^
        std::rotl(static_cast<std::uint64_t>(value >> 64), 29);
    hash ^= hash >> 30;
    hash *= 0xbf58476d1ce4e5b9ULL;
    hash ^= hash >> 27;
    hash *= 0x94d049bb133111ebULL;
    return hash ^ (hash >> 31);
}

struct TableHash {
    std::size_t operator()(Table value) const { return hashTable(value); }
};

struct StateHash {
    std::size_t operator()(const State& state) const {
        std::size_t result = state.remaining;
        for (Table value : state.values) {
            result = std::rotl(result, 9) ^ hashTable(value);
        }
        return result;
    }
};

Probes combine(Probes a, const Probes& b) {
    for (std::size_t i = 0; i < a.size(); ++i) {
        a[i] |= b[i];
    }
    return a;
}

struct Problem {
    std::array<Table, inputCount> inputs{};
    Table target = 0;
    std::vector<std::pair<int, int>> probes;
    Probes full{};

    Problem() {
        std::array<bool, 128> positive{};
        for (int x = 0; x < 128; ++x) {
            for (int i = 0; i < inputCount; ++i) {
                if ((x >> i) & 1) {
                    inputs[i] |= Table{1} << x;
                }
            }
            for (const auto& [a, b] : edges) {
                if (((x >> a) & 1) && ((x >> b) & 1)) {
                    positive[x] = true;
                    target |= Table{1} << x;
                    break;
                }
            }
        }
        for (int x = 0; x < 128; ++x) {
            if (positive[x]) {
                continue;
            }
            bool maximal = true;
            for (int i = 0; i < inputCount; ++i) {
                if ((x >> i) & 1) {
                    continue;
                }
                const int y = x | (1 << i);
                if (positive[y]) {
                    probes.emplace_back(x, y);
                } else {
                    maximal = false;
                }
            }
            if (maximal) {
                for (const auto& [a, b] : edges) {
                    probes.emplace_back(x, (1 << a) | (1 << b));
                }
            }
        }
        std::sort(probes.begin(), probes.end());
        probes.erase(std::unique(probes.begin(), probes.end()), probes.end());
        if (probes.size() > full.size() * 64) {
            std::abort();
        }
        for (std::size_t i = 0; i < probes.size(); ++i) {
            full[i / 64] |= std::uint64_t{1} << (i % 64);
        }
    }

    Probes separates(Table value) const {
        Probes result{};
        for (std::size_t i = 0; i < probes.size(); ++i) {
            const auto [a, b] = probes[i];
            if (((value >> a) ^ (value >> b)) & 1) {
                result[i / 64] |= std::uint64_t{1} << (i % 64);
            }
        }
        return result;
    }
};

struct Search {
    const Problem& problem;
    bool freeInversion;
    std::atomic<bool>& found;
    std::mutex& outputMutex;
    std::vector<Gate> gates;
    std::unordered_map<Table, Probes, TableHash> knownProbes;
    std::unordered_set<State, StateHash> failed;
    std::uint64_t visits = 0;

    Probes separates(Table value) {
        if (const auto hit = knownProbes.find(value); hit != knownProbes.end()) {
            return hit->second;
        }
        const Probes result = problem.separates(value);
        if (knownProbes.size() < cacheLimit) {
            knownProbes.emplace(value, result);
        }
        return result;
    }

    bool advance(const std::vector<Wire>& wires, int remaining, std::size_t a,
                 std::size_t b, Table value, Gate gate) {
        if (freeInversion && (value & 1)) {
            value = ~value;
            gate.op = static_cast<char>(gate.op - 'a' + 'A');
        }
        if (!value || value == ~Table{0} ||
            std::any_of(wires.begin(), wires.end(), [value](const Wire& wire) {
                return wire.value == value;
            })) {
            return false;
        }
        if (value == problem.target) {
            std::lock_guard guard(outputMutex);
            if (!found.exchange(true)) {
                std::cout << "FOUND " << (freeInversion ? "free-inversion " : "AND/OR ")
                          << gates.size() + 1 << '\n';
                for (const Gate& earlier : gates) {
                    std::cout << earlier.op << ' ' << earlier.a << ' ' << earlier.b << '\n';
                }
                std::cout << gate.op << ' ' << gate.a << ' ' << gate.b << std::endl;
            }
            return true;
        }
        if (remaining == 1) {
            return false;
        }
        std::vector<Wire> next;
        next.reserve(wires.size() + 1);
        const Wire fresh{value, separates(value), inputCount + static_cast<int>(gates.size())};
        next.push_back(fresh);
        Probes covered = fresh.distinguishes;
        for (std::size_t i = 0; i < wires.size(); ++i) {
            if (i != a && i != b) {
                next.push_back(wires[i]);
                covered = combine(covered, wires[i].distinguishes);
            }
        }
        gates.push_back(gate);
        for (int keep = 0; keep < 4; ++keep) {
            next.resize(wires.size() - 1);
            Probes branch = covered;
            if (keep & 1) {
                next.push_back(wires[a]);
                branch = combine(branch, wires[a].distinguishes);
            }
            if (keep & 2) {
                next.push_back(wires[b]);
                branch = combine(branch, wires[b].distinguishes);
            }
            if (next.size() <= static_cast<std::size_t>(remaining) &&
                branch == problem.full && solve(next, remaining - 1)) {
                return true;
            }
        }
        gates.pop_back();
        return false;
    }

    bool pair(const std::vector<Wire>& wires, int remaining, std::size_t a, std::size_t b) {
        const auto& x = wires[a];
        const auto& y = wires[b];
        if (!freeInversion) {
            return advance(wires, remaining, a, b, x.value & y.value, {'a', x.index, y.index}) ||
                   advance(wires, remaining, a, b, x.value | y.value, {'o', x.index, y.index});
        }
        for (int signs = 0; signs < 4; ++signs) {
            const bool left = signs & 1;
            const bool right = signs & 2;
            const Table value = (left ? ~x.value : x.value) & (right ? ~y.value : y.value);
            if (advance(wires, remaining, a, b, value,
                        {'a', left ? -x.index - 1 : x.index, right ? -y.index - 1 : y.index})) {
                return true;
            }
        }
        return false;
    }

    bool solve(const std::vector<Wire>& wires, int remaining) {
        if (found.load(std::memory_order_relaxed)) {
            return true;
        }
        ++visits;
        State state{{}, remaining};
        for (std::size_t i = 0; i < wires.size(); ++i) {
            state.values[i] = wires[i].value;
        }
        std::sort(state.values.begin(), state.values.begin() + wires.size());
        if (failed.contains(state)) {
            return false;
        }
        for (std::size_t a = 0; a < wires.size(); ++a) {
            for (std::size_t b = a + 1; b < wires.size(); ++b) {
                if (pair(wires, remaining, a, b)) {
                    return true;
                }
            }
        }
        if (failed.size() < cacheLimit) {
            failed.insert(state);
        }
        return false;
    }
};

int main(int argc, char** argv) {
    const bool freeInversion = argc > 1 && std::string_view(argv[1]) == "free";
    const int limit = argc > 2 ? std::atoi(argv[2]) : budget;
    if (limit < 1 || limit > maxBudget) {
        return 2;
    }
    const Problem problem;
    std::vector<Wire> inputs;
    std::vector<std::pair<int, int>> roots;
    for (int a = 0; a < inputCount; ++a) {
        inputs.push_back({problem.inputs[a], problem.separates(problem.inputs[a]), a});
        for (int b = a + 1; b < inputCount; ++b) {
            roots.emplace_back(a, b);
        }
    }
    std::cout << roots.size() << " first gate pairs, " << problem.probes.size()
              << " probes, budget " << limit << std::endl;
    std::atomic<bool> found = false;
    std::atomic<std::size_t> next = 0;
    std::mutex outputMutex;
    {
        std::vector<std::jthread> workers;
        for (int i = 0; i < 6; ++i) {
            workers.emplace_back([&] {
                Search search{problem, freeInversion, found, outputMutex};
                while (!found.load()) {
                    const std::size_t root = next.fetch_add(1);
                    if (root >= roots.size()) {
                        return;
                    }
                    const auto [a, b] = roots[root];
                    const auto start = search.visits;
                    if (!search.pair(inputs, limit, a, b)) {
                        std::lock_guard guard(outputMutex);
                        std::cout << "EXHAUSTED " << a << ' ' << b << ' '
                                  << search.visits - start << " states" << std::endl;
                    }
                }
            });
        }
    }
    std::cout << (found ? "RESULT found" : "RESULT no circuit") << std::endl;
}
