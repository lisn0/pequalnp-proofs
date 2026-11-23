#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <unordered_map>
#include <utility>

constexpr int vertices = 10;
constexpr std::pair<int, int> graph[] = {
    {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {0, 5}, {1, 6}, {2, 7},
    {3, 8}, {4, 9}, {5, 7}, {7, 9}, {9, 6}, {6, 8}, {8, 5},
};
constexpr int totalEdges = std::size(graph);

struct State {
    unsigned edges;
    unsigned singles;

    bool constant() const { return edges == 0 && singles == 0; }
};

int forest_bound(State state) {
    if (state.edges == 0) return std::max(0, std::popcount(state.singles) - 1);
    std::array<int, vertices> part{};
    for (int v = 0; v < vertices; ++v) part[v] = v;
    for (int i = 0; i < totalEdges; ++i) {
        if ((state.edges & (1u << i)) == 0) continue;
        auto [u, v] = graph[i];
        int old = part[u], dest = part[v];
        if (old == dest) return 0;
        for (auto& p : part) if (p == old) p = dest;
    }
    int cover = vertices;
    for (unsigned selected = 0; selected < (1u << vertices); ++selected) {
        if (std::popcount(selected) >= cover) continue;
        bool meets = true;
        for (int i = 0; i < totalEdges; ++i) {
            if ((state.edges & (1u << i)) == 0) continue;
            auto [u, v] = graph[i];
            if ((selected & ((1u << u) | (1u << v))) == 0) {
                meets = false;
                break;
            }
        }
        if (meets) cover = std::popcount(selected);
    }
    return std::popcount(state.edges) + cover + std::popcount(state.singles) - 1;
}

unsigned support(State state) {
    unsigned mask = state.singles;
    for (int i = 0; i < totalEdges; ++i) {
        if (state.edges & (1u << i)) {
            auto [u, v] = graph[i];
            mask |= (1u << u) | (1u << v);
        }
    }
    return mask;
}

State restrict_vertex(State state, int vertex, bool value) {
    if (value && (state.singles & (1u << vertex))) return {0, 0};
    state.singles &= ~(1u << vertex);
    for (int i = 0; i < totalEdges; ++i) {
        if ((state.edges & (1u << i)) == 0) continue;
        auto [u, v] = graph[i];
        if (u == vertex || v == vertex) {
            state.edges &= ~(1u << i);
            if (value) state.singles |= 1u << (u == vertex ? v : u);
        }
    }
    for (int i = 0; i < totalEdges; ++i) {
        auto [u, v] = graph[i];
        if (state.singles & ((1u << u) | (1u << v))) state.edges &= ~(1u << i);
    }
    return state;
}

int lower(State state, std::unordered_map<unsigned, int>& results, bool seed_forests) {
    unsigned key = (state.edges << vertices) | state.singles;
    if (auto it = results.find(key); it != results.end()) return it->second;
    unsigned mask = support(state);
    if (std::popcount(mask) <= 1) return 0;
    int best = std::popcount(mask) - 1;
    if (seed_forests) best = std::max(best, forest_bound(state));
    for (int v = 0; v < vertices; ++v) {
        if ((mask & (1u << v)) == 0) continue;
        State left = restrict_vertex(state, v, false);
        State right = restrict_vertex(state, v, true);
        int a = lower(left, results, seed_forests);
        int b = lower(right, results, seed_forests);
        best = std::max(best, std::max(a, b) + 1);
        if (!left.constant() && !right.constant()) best = std::max(best, std::min(a, b) + 2);
    }
    results.emplace(key, best);
    return best;
}

int main() {
    for (bool seed : {false, true}) {
        std::unordered_map<unsigned, int> results;
        int value = lower({(1u << totalEdges) - 1, 0}, results, seed);
        std::cout << (seed ? "With forest bounds: " : "With support bounds: ")
                  << value << " across " << results.size() << " states\n";
    }
}
