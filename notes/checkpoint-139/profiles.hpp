// Enumerate all integral degree profiles using the parity of the extra incidences.
#pragma once
#include "board.hpp"

struct Parities {
    std::array<std::array<std::vector<Mask>, 22>, 1024> byWeight;
    std::array<unsigned, 21> column{};
    std::array<std::array<unsigned, 128>, 3> chunks{};

    void build(const Board &board, int side) {
        std::array<Mask, 21> basis{};
        int rank = 0;
        for (int j = 0; j < 21; ++j) {
            Mask line = full ^ board.sites[21 * (1 - side) + j].zeros, v = line;
            while (v) {
                int k = std::bit_width(v) - 1;
                if (basis[k]) {
                    v ^= basis[k];
                    continue;
                }
                basis[k] = v;
                for (Mask m = line; m; m &= m - 1)
                    column[std::countr_zero(m)] |= 1u << rank;
                ++rank;
                break;
            }
        }
        check(rank == 10, "Wrong binary incidence rank");
        for (int k = 0; k < 3; ++k)
            for (unsigned w = 1; w < 128; ++w)
                chunks[k][w] = chunks[k][w & (w - 1)] ^ column[k * 7 + std::countr_zero(w)];
        for (Mask w = 0; w <= full; ++w)
            byWeight[syndrome(w)][std::popcount(w)].push_back(w);
    }
    unsigned syndrome(Mask w) const {
        return chunks[0][w & 127] ^ chunks[1][(w >> 7) & 127] ^ chunks[2][w >> 14];
    }
    int choices(unsigned s, int slack) const {
        int count = 0;
        for (int weight = slack % 2; weight <= std::min(slack, 21); weight += 2)
            count += byWeight[s][weight].size();
        return count;
    }
};

struct FilterCounts {
    Word local = 0, domination = 0, parity = 0, balance = 0, feasible = 0, profiles = 0, states = 0;
};

struct Profiles {
    const Board &board;
    std::array<Parities, 2> codes{};
    std::array<std::array<std::array<Mask, 128>, 3>, 2> neighbors{};
    explicit Profiles(const Board &b) : board(b) {
        for (int s = 0; s < 2; ++s) {
            codes[s].build(b, s);
            for (int k = 0; k < 3; ++k)
                for (Mask w = 1; w < 128; ++w)
                    neighbors[s][k][w] =
                        neighbors[s][k][w & (w - 1)] |
                        (full ^ board.sites[21 * s + 7 * k + std::countr_zero(w)].zeros);
        }
    }
    Mask pencil(int side, Mask w) const {
        return neighbors[side][0][w & 127] | neighbors[side][1][(w >> 7) & 127] |
               neighbors[side][2][w >> 14];
    }
    template <class F>
    bool extra(int side, int m, const Margins &low, Margins &d, int units, int first,
               F &visit) const {
        if (!units)
            return visit(d);
        for (int bit = first; bit < 21; ++bit) {
            int v = 21 * side + bit;
            if (d[v] + 2 > m)
                continue;
            const auto &points = board.sites[v].incident;
            if (std::any_of(points.begin(), points.end(), [&](int j) { return d[j] <= low[j]; }))
                continue;
            d[v] += 2;
            for (int j : points)
                --d[j];
            bool found = extra(side, m, low, d, units - 1, bit, visit);
            d[v] -= 2;
            for (int j : points)
                ++d[j];
            if (found)
                return true;
        }
        return false;
    }
    template <class F>
    bool enumerate(int m, const Residual &target, FilterCounts &stats, F &visit) const {
        Margins low{};
        for (int i = 0; i < 42; ++i)
            low[i] = board.sites[i].minimum[target[i]];
        return bounds(m, low, stats, visit);
    }

    template <class F> bool bounds(int m, const Margins &low, FilterCounts &stats, F &visit) const {
        std::array<int, 2> slack{6 * m, 6 * m};
        std::array<Mask, 2> light{}, odd{};
        for (int i = 0; i < 42; ++i) {
            int d = low[i];
            int s = i / 21;
            slack[s] -= d;
            light[s] |= Mask(d <= 2) << (i % 21);
            odd[s] |= Mask(d % 2) << (i % 21);
        }
        if (std::min(slack[0], slack[1]) < 0) {
            ++stats.local;
            return false;
        }
        if (m <= 10 && ((pencil(0, light[0]) | light[1]) != full ||
                        (pencil(1, light[1]) | light[0]) != full)) {
            ++stats.domination;
            return false;
        }
        std::array<unsigned, 2> syn{codes[0].syndrome(odd[0]), codes[1].syndrome(odd[1])};
        std::array<int, 2> options{codes[0].choices(syn[0], slack[0]),
                                   codes[1].choices(syn[1], slack[1])};
        if (!options[0] || !options[1]) {
            ++stats.parity;
            return false;
        }
        int side = options[0] <= options[1] ? 0 : 1, other = 1 - side;
        const auto &masks = codes[side].byWeight[syn[side]];
        Word start = stats.profiles;
        auto leaf = [&](const Margins &d) {
            ++stats.profiles;
            return visit(d);
        };
        for (int w = slack[side] % 2; w <= std::min(21, slack[side]); w += 2)
            for (Mask correction : masks[w]) {
                Margins d = low;
                for (Mask x = correction; x; x &= x - 1)
                    ++d[21 * side + std::countr_zero(x)];
                bool ok = true;
                for (int j = 21 * other; j < 21 * other + 21; ++j) {
                    int sum = 0;
                    for (int i : board.sites[j].incident)
                        sum += d[i];
                    check(!(sum % 2), "Odd incidence sum after syndrome correction");
                    d[j] = m - sum / 2;
                    if (d[j] < low[j]) {
                        ok = false;
                        break;
                    }
                }
                if (ok && extra(side, m, low, d, (slack[side] - w) / 2, 0, leaf))
                    return true;
            }
        if (start == stats.profiles)
            ++stats.balance;
        else
            ++stats.feasible;
        return false;
    }
};
