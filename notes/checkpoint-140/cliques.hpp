// The vertices are the zero cells. Two zeros conflict when a crossed entry is one.
#pragma once
#include "common.hpp"
#include <span>
template <int N> struct Bits {
    static constexpr int width = (N + 63) / 64;
    std::array<Word, width> w{};
    void set(int i) {
        w[i / 64] |= Word{1} << (i % 64);
    }
    void erase(int i) {
        w[i / 64] &= ~(Word{1} << (i % 64));
    }
    bool has(int i) const {
        return (w[i / 64] >> (i % 64)) & 1;
    }
    bool any() const {
        for (auto a : w)
            if (a)
                return true;
        return false;
    }
    int count() const {
        int n = 0;
        for (auto a : w)
            n += std::popcount(a);
        return n;
    }
    Bits operator&(const Bits &b) const {
        Bits out;
        for (int i = 0; i < width; ++i)
            out.w[i] = w[i] & b.w[i];
        return out;
    }
    Bits operator|(const Bits &b) const {
        Bits out;
        for (int i = 0; i < width; ++i)
            out.w[i] = w[i] | b.w[i];
        return out;
    }
    void remove(const Bits &b) {
        for (int i = 0; i < width; ++i)
            w[i] &= ~b.w[i];
    }
    template <class F> void each(F f) const {
        for (int i = 0; i < width; ++i)
            for (Word b = w[i]; b; b &= b - 1)
                f(64 * i + std::countr_zero(b));
    }
    int pop() {
        for (int i = 0; i < width; ++i)
            if (w[i]) {
                int v = 64 * i + std::countr_zero(w[i]);
                w[i] &= w[i] - 1;
                return v;
            }
        return -1;
    }
    static Bits full() {
        Bits a;
        for (int i = 0; i < N; ++i)
            a.set(i);
        return a;
    }
};
using HSet = Bits<168>;
using Cells = Bits<336>;
struct CliqueTable {
    std::vector<HSet> missing;
    std::array<std::vector<Word>, 168> indices;
    void finish() {
        for (auto &list : indices)
            list.resize((missing.size() + 63) / 64);
        for (std::size_t k = 0; k < missing.size(); ++k)
            missing[k].each([&](int h) { indices[h][k / 64] |= Word{1} << (k % 64); });
    }
    template <class F> void unhit(const std::array<int, 6> &s, F visit) const {
        const auto *a = indices[s[0]].data(), *b = indices[s[1]].data(), *c = indices[s[2]].data();
        const auto *d = indices[s[3]].data(), *e = indices[s[4]].data(), *f = indices[s[5]].data();
        for (std::size_t k = 0; k < indices[0].size(); ++k)
            for (Word v = a[k] & b[k] & c[k] & d[k] & e[k] & f[k]; v; v &= v - 1)
                visit(missing[64 * k + std::countr_zero(v)]);
    }
};
struct Conflicts {
    std::array<std::array<int, 2>, 336> cell;
    std::array<Cells, 336> neighbor{};
    std::array<Cells, 168> boxes{};
    std::array<HSet, 336> through{};
    std::array<Word, 9> cliqueCount{};
    CliqueTable six, seven;
    explicit Conflicts(const Geometry &b) {
        int n = 0;
        for (int r = 0; r < 21; ++r)
            for (int c = 0; c < 21; ++c)
                if (b.rows[r] >> c & 1)
                    cell[n++] = {r, c};
        require(n == 336, "Wrong zero-cell inventory");
        for (int i = 0; i < n; ++i) {
            auto [r, c] = cell[i];
            for (int j = 0; j < n; ++j) {
                auto [p, q] = cell[j];
                if (!((b.rows[r] >> q) & (b.rows[p] >> c) & 1))
                    neighbor[i].set(j);
            }
            for (int j = 0; j < 168; ++j)
                if ((b.maximum[j][0] >> r) & (b.maximum[j][1] >> c) & 1) {
                    boxes[j].set(i);
                    through[i].set(j);
                }
            require(through[i].count() == 18 && neighbor[i].count() == 140,
                    "Incorrect cell degree");
        }
        enumerate(Cells::full(), HSet::full(), 0);
        require(cliqueCount ==
                    std::array<Word, 9>{1, 336, 23520, 411040, 1473360, 941472, 60480, 2880, 0},
                "Wrong clique inventory");
        six.finish();
        seven.finish();
    }
    void enumerate(Cells left, HSet misses, int k) {
        ++cliqueCount[k];
        if (k == 6 || k == 7) {
            require(misses.count() == 168 - 18 * k, "A maximum rectangle meets a clique twice");
            (k == 6 ? six : seven).missing.push_back(misses);
        }
        if (k == 8)
            return;
        while (left.any()) {
            int v = left.pop();
            HSet m = misses;
            m.remove(through[v]);
            enumerate(left & neighbor[v], m, k + 1);
        }
    }
    bool clique(Cells left, int need) const {
        if (need == 1)
            return left.any();
        while (left.count() >= need) {
            int v = left.pop();
            if (clique(left & neighbor[v], need - 1))
                return true;
        }
        return false;
    }
};
struct Seed {
    std::array<int, 6> h{};
    Word weight;
};
inline std::vector<Seed> readSeeds(const char *path) {
    std::ifstream input(path);
    require(input.good(), "Missing six-subset list");
    std::vector<Seed> seeds;
    Seed s;
    Word mass = 0;
    while (input >> s.h[0]) {
        for (int j = 1; j < 6; ++j)
            require(bool(input >> s.h[j]), "Truncated six-subset");
        require(bool(input >> s.weight) && s.weight > 0 && 241920 % s.weight == 0 && s.h[0] >= 0 &&
                    s.h.back() < 168 && std::is_sorted(s.h.begin(), s.h.end()) &&
                    std::adjacent_find(s.h.begin(), s.h.end()) == s.h.end(),
                "Invalid six-subset");
        seeds.push_back(s);
        mass += s.weight;
    }
    require(mass == 28530983404ULL, "Incomplete six-subset inventory");
    return seeds;
}
