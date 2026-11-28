// Color the residual conflict graph. One color class extends to its row-by-column product.
#pragma once
#include "cliques.hpp"

template <int K> struct Coloring {
    struct State {
        Cells left;
        std::array<Cells, K> allowed, members;
    };
    const Conflicts &g;
    Word nodes = 0;
    std::array<Cells, K> answer;
    explicit Coloring(const Conflicts &graph) : g(graph) {}
    bool find(Cells left, int n, std::array<int, K> &out) const {
        while (left.count() >= n) {
            int v = left.pop();
            out[n - 1] = v;
            if (n == 1 || find(left & g.neighbor[v], n - 1, out))
                return true;
        }
        return false;
    }
    bool assign(State &s, int v, int color) const {
        if (!s.allowed[color].has(v))
            return false;
        s.left.erase(v);
        s.members[color].set(v);
        s.allowed[color].remove(g.neighbor[v]);
        return true;
    }
    bool solve(State &s) {
        ++nodes;
        while (s.left.any()) {
            Cells forced, twos;
            int impossible = 0;
            for (int w = 0; w < Cells::width; ++w) {
                Word one = 0, two = 0, three = 0;
                for (auto &a : s.allowed) {
                    Word t = a.w[w];
                    three |= two & t;
                    two |= one & t;
                    one |= t;
                }
                if (s.left.w[w] & ~one)
                    impossible = 1;
                forced.w[w] = s.left.w[w] & ~two;
                twos.w[w] = s.left.w[w] & ~three;
            }
            if (impossible)
                return false;
            if (forced.any()) {
                while (forced.any()) {
                    int v = forced.pop(), i = 0;
                    while (i < K && !s.allowed[i].has(v))
                        ++i;
                    if (i == K)
                        return false;
                    assign(s, v, i);
                }
                continue;
            }
            int best = -1, count = K + 1, degree = -1;
            const auto candidates = twos.any() ? twos : s.left;
            candidates.each([&](int v) {
                int n = 0;
                for (const auto &a : s.allowed)
                    n += a.has(v);
                if (n <= count) {
                    int d = (s.left & g.neighbor[v]).count();
                    if (n < count || d > degree) {
                        best = v;
                        count = n;
                        degree = d;
                    }
                }
            });
            bool usedFree = false;
            for (int c = 0; c < K; ++c)
                if (s.allowed[c].has(best)) {
                    if (!s.members[c].any()) {
                        if (usedFree)
                            continue;
                        usedFree = true;
                    }
                    State next = s;
                    assign(next, best, c);
                    if (solve(next))
                        return true;
                }
            return false;
        }
        answer = s.members;
        return true;
    }
    bool cover(Cells missing) {
        State s{};
        s.left = missing;
        s.allowed.fill(missing);
        if (missing.any()) {
            std::array<int, K> witness{};
            int n = K;
            while (n > 1 && !find(missing, n, witness))
                --n;
            if (n == 1)
                witness[0] = missing.pop();
            for (int i = 0; i < n; ++i)
                require(assign(s, witness[i], i), "Invalid starting clique");
        }
        return solve(s);
    }
};

struct Scores {
    int weight[168][168]{};
    explicit Scores(const Geometry &board) {
        for (int i = 0; i < 168; ++i)
            for (int j = 0; j < i; ++j) {
                int n = std::popcount(board.maximum[i][0] & board.maximum[j][0]);
                require(n == std::popcount(board.maximum[i][1] & board.maximum[j][1]) && n <= 3,
                        "Invalid invariant overlap");
                weight[i][j] = weight[j][i] = 1 << (4 * n);
            }
    }
    std::array<int, 6> base(const std::array<int, 6> &s) const {
        std::array<int, 6> out{};
        for (int a = 0; a < 6; ++a)
            for (int b = 0; b < 6; ++b)
                out[a] += weight[s[a]][s[b]];
        return out;
    }
    template <int N>
    bool canonical(const std::array<int, 6> &s, const std::array<int, 6> &prev,
                   const std::array<int, N> &extra) const {
        std::array<int, N> v{};
        auto u = prev;
        for (int a = 0; a < N; ++a) {
            for (int b = 0; b < 6; ++b) {
                int d = weight[extra[a]][s[b]];
                u[b] += d;
                v[a] += d;
            }
            for (int b = 0; b < N; ++b)
                v[a] += weight[extra[a]][extra[b]];
        }
        return *std::max_element(u.begin(), u.end()) <= *std::min_element(v.begin(), v.end());
    }
};
