// Local incidence data for the posted 21 by 21 matrix.
#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
using CellMask = std::uint16_t;
using Word = std::uint64_t;
constexpr Mask full = (1u << 21) - 1;
using Margins = std::array<int, 42>;
using Residual = std::array<CellMask, 42>;

inline void check(bool yes, const char *message) {
    if (!yes)
        throw std::runtime_error(message);
}

struct Family {
    std::array<Word, 3> words{};
    void set(int j) {
        words[j / 64] |= Word{1} << (j % 64);
    }
    void erase(int j) {
        words[j / 64] &= ~(Word{1} << (j % 64));
    }
    bool has(int j) const {
        return words[j / 64] >> (j % 64) & 1;
    }
    int count() const {
        return std::popcount(words[0]) + std::popcount(words[1]) + std::popcount(words[2]);
    }
    Family operator&(const Family &b) const {
        return {{words[0] & b.words[0], words[1] & b.words[1], words[2] & b.words[2]}};
    }
    Family without(const Family &b) const {
        return {{words[0] & ~b.words[0], words[1] & ~b.words[1], words[2] & ~b.words[2]}};
    }
    template <class F> void each(F f) const {
        for (int k = 0; k < 3; ++k)
            for (Word m = words[k]; m; m &= m - 1)
                f(64 * k + std::countr_zero(m));
    }
};

struct Box {
    std::array<Mask, 2> axes{};
    Residual cover{};
    Word key() const {
        return axes[0] | (Word(axes[1]) << 21);
    }
};
struct Site {
    Mask zeros{};
    std::array<int, 5> incident{};
    std::array<int, 16> coordinates{};
    Family through;
    std::array<Family, 16> entries{};
    std::array<unsigned char, 65536> minimum{};
    std::array<Family, 65536> singles{};
};

struct Board {
    std::array<Site, 42> sites{};
    std::array<Box, 168> maximum{};
    std::array<std::array<int, 12>, 168> membership{};
    Family all;

    Box box(Mask a, Mask b) const {
        check(a && b && a <= full && b <= full, "Invalid rectangle sides");
        Box out{{a, b}, {}};
        for (int side = 0; side < 2; ++side) {
            Mask other = out.axes[1 - side];
            for (Mask z = out.axes[side]; z; z &= z - 1) {
                int v = 21 * side + std::countr_zero(z);
                const Site &s = sites[v];
                check(!(other & ~s.zeros), "Rectangle contains a one");
                for (int j = 0; j < 16; ++j)
                    if (other >> s.coordinates[j] & 1)
                        out.cover[v] |= 1u << j;
            }
        }
        return out;
    }

    void read(std::istream &in) {
        for (int i = 0; i < 21; ++i) {
            Mask m;
            check(bool(in >> m) && m <= full && std::popcount(m) == 16, "Board row differs");
            sites[i].zeros = m;
            for (Mask x = m; x; x &= x - 1)
                sites[21 + std::countr_zero(x)].zeros |= 1u << i;
        }
        for (int i = 0; i < 42; ++i) {
            Site &s = sites[i];
            check(std::popcount(s.zeros) == 16, "Board column differs");
            int k = 0;
            for (Mask m = s.zeros; m; m &= m - 1)
                s.coordinates[k++] = std::countr_zero(m);
            k = 0;
            for (Mask m = full ^ s.zeros; m; m &= m - 1)
                s.incident[k++] = (i < 21 ? 21 : 0) + std::countr_zero(m);
        }
        for (int j = 0; j < 168; ++j) {
            Mask a, b;
            check(bool(in >> a >> b) && std::popcount(a) == 6 && std::popcount(b) == 6,
                  "Wrong maximum rectangle");
            auto &h = maximum[j];
            h = box(a, b);
            check(j == 0 || maximum[j - 1].axes < h.axes, "Maximum rectangles are not ordered");
            all.set(j);
            int k = 0;
            for (int i = 0; i < 42; ++i) {
                const int side = i / 21;
                int incidence = std::popcount(h.axes[1 - side] & (full ^ sites[i].zeros));
                check(2 * int((h.axes[side] >> (i % 21)) & 1) + incidence == 2,
                      "Point-line balance failed");
                if (!h.cover[i])
                    continue;
                auto &s = sites[i];
                s.through.set(j);
                membership[j][k++] = i;
                for (unsigned m = h.cover[i]; m; m &= m - 1)
                    s.entries[std::countr_zero(m)].set(j);
            }
            check(k == 12, "Incorrect maximum rectangle membership");
        }
        for (int i = 0; i < 42; ++i) {
            auto &s = sites[i];
            s.minimum.fill(3);
            s.minimum[0] = 0;
            s.singles[0] = s.through;
            bool triple = false;
            s.through.each([&](int a) {
                auto p = maximum[a].cover[i];
                s.minimum[p] = 1;
                s.through.each([&](int b) {
                    if (a == b)
                        return;
                    auto q = maximum[b].cover[i];
                    int joint = p | q;
                    check(std::popcount(unsigned(joint)) <= 11,
                          "Two maximum rectangles cover twelve local cells");
                    s.minimum[joint] = std::min<int>(s.minimum[joint], 2);
                    if (!triple)
                        s.through.each([&](int c) {
                            if ((joint | maximum[c].cover[i]) == 65535)
                                triple = true;
                        });
                });
            });
            check(triple, "A full local three-cover was not found");
            for (int bit = 1; bit < 65536; bit *= 2)
                for (int start = 0; start < 65536; start += 2 * bit)
                    for (int n = start; n < start + bit; ++n)
                        s.minimum[n] = std::min(s.minimum[n], s.minimum[n + bit]);
            for (unsigned m = 1; m < 65536; ++m)
                s.singles[m] = s.singles[m & (m - 1)] & s.entries[std::countr_zero(m)];
        }
    }
};
