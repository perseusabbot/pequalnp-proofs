#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Perm = std::array<unsigned char, 168>;
using Axes = std::array<unsigned, 2>;

inline void require(bool ok, const char *message) {
    if (!ok)
        throw std::runtime_error(message);
}

struct Geometry {
    std::array<unsigned, 21> rows{};
    std::array<Axes, 168> maximum{};
    std::vector<Perm> generators;
    explicit Geometry(const char *path) {
        std::ifstream in(path);
        for (auto &row : rows)
            require(bool(in >> row) && row < (1u << 21) && std::popcount(row) == 16,
                    "Invalid board row");
        for (auto &[r, c] : maximum) {
            require(bool(in >> r >> c) && r < (1u << 21) && c < (1u << 21) &&
                        std::popcount(r) == 6 && std::popcount(c) == 6,
                    "Invalid maximum rectangle");
            for (unsigned t = r; t; t &= t - 1)
                require(!(c & ~rows[std::countr_zero(t)]), "Rectangle contains a one");
        }
        require(std::is_sorted(maximum.begin(), maximum.end()) &&
                    std::adjacent_find(maximum.begin(), maximum.end()) == maximum.end(),
                "Unordered maximum rectangles");
        int count;
        require(bool(in >> count) && count >= 1 && count <= 10, "Invalid generator count");
        for (int i = 0; i < count; ++i) {
            Perm p{};
            std::array<bool, 168> seen{};
            for (auto &v : p) {
                int x;
                require(bool(in >> x) && x >= 0 && x < 168 && !seen[x], "Invalid permutation");
                seen[x] = true;
                v = x;
            }
            generators.push_back(p);
        }
    }
};
