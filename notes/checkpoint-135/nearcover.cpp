// Complete a specified part of the incumbent while allowing one uncovered zero.
#include <algorithm>
#include <array>
#include <string>
#include <charconv>
#include <bit>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using Mask = std::uint32_t;
struct Cell { int row, col; Mask rectangles; };

struct Coloring {
    int limit;
    std::vector<std::vector<int>> adjacent;
    std::vector<int> color;
    std::vector<Mask> forbidden;
    std::vector<std::array<unsigned, 14>> counts;
    std::uint64_t nodes = 0;

    bool assign(int remaining, int used, bool canSkip) {
        if (!remaining) return true;
        ++nodes;
        int vertex = -1;
        std::pair<int, int> best{-1, -1};
        for (int v = 0; v < int(color.size()); ++v) {
            if (color[v] != -1) continue;
            std::pair<int, int> score{std::popcount(forbidden[v]), int(adjacent[v].size())};
            if (score.first == limit && !canSkip) return false;
            if (score > best) { vertex = v; best = score; }
        }
        // Permuting the unused color names changes no constraint.
        for (int c = 0; c < std::min(used + 1, limit); ++c) {
            Mask bit = Mask{1} << c;
            if (forbidden[vertex] & bit) continue;
            color[vertex] = c;
            for (int w : adjacent[vertex]) {
                if (!counts[w][c]++) forbidden[w] |= bit;
            }
            if (assign(remaining-1, std::max(used, c+1), canSkip)) return true;
            for (int w : adjacent[vertex]) {
                if (!--counts[w][c]) forbidden[w] ^= bit;
            }
            color[vertex] = -1;
        }
        // The marked vertex consumes the sole allowed uncovered cell.
        if (canSkip) {
            color[vertex] = -2;
            if (assign(remaining-1, used, false)) return true;
            color[vertex] = -1;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    bool anywhere = argc == 2 && std::string(argv[1]) == "--any-hole";
    int holeRow = -1, holeCol = -1;
    if (!anywhere) {
        if (argc != 4 || std::string(argv[1]) != "--hole") return 1;
        auto parse = [](const std::string& arg, int& out) {
            auto [end, error] = std::from_chars(arg.data(), arg.data()+arg.size(), out);
            return error == std::errc{} && end == arg.data()+arg.size() && out >= 0 && out < 21;
        };
        if (!parse(argv[2], holeRow) || !parse(argv[3], holeCol)) return 1;
    }
    int n, k, removedCount;
    if (!(std::cin >> n >> k >> removedCount) || n != 21 || k != 14 ||
        removedCount < 1 || removedCount > k) return 1;
    std::vector<Mask> rows(n);
    for (auto &row : rows) if (!(std::cin >> row)) return 1;
    if (!anywhere && !((rows[holeRow] >> holeCol) & 1u)) return 1;
    std::vector<std::pair<Mask, Mask>> incumbent(k);
    for (auto &[a,b] : incumbent) if (!(std::cin >> a >> b)) return 1;
    const Mask full = (1u << k) - 1;
    std::vector<Cell> board;
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j) {
            Mask owners = 0;
            for (int t = 0; t < k; ++t)
                if ((incumbent[t].first >> i) & (incumbent[t].second >> j) & 1u)
                    owners |= 1u << t;
            if ((rows[i] >> j) & 1u) {
                if (i != holeRow || j != holeCol) board.push_back({i,j,owners});
            }
            else if (owners) return 1;
        }

    std::uint64_t total = 0, largest = 0;
    unsigned windows = 0;
    for (Mask removed = 0; removed <= full; ++removed) {
        if (std::popcount(removed) != removedCount) continue;
        std::vector<Cell> need;
        for (auto cell : board)
            if (!(cell.rectangles & (full ^ removed))) need.push_back(cell);
        const int m = need.size();
        Coloring solver{removedCount, std::vector<std::vector<int>>(m),
            std::vector<int>(m,-1), std::vector<Mask>(m), std::vector<std::array<unsigned,14>>(m)};
        for (int v = 0; v < m; ++v)
            for (int w = 0; w < v; ++w) {
                // Two zeros fit in one rectangle exactly when both crossed entries are zero.
                if ((rows[need[v].row] >> need[w].col) & (rows[need[w].row] >> need[v].col) & 1u) continue;
                solver.adjacent[v].push_back(w);
                solver.adjacent[w].push_back(v);
            }
        if (solver.assign(m,0,anywhere)) {
            std::cout << "COVER " << removed << '\n';
            for (int t = 0; t < k; ++t)
                if (!(removed & (1u << t))) std::cout << incumbent[t].first << ' ' << incumbent[t].second << '\n';
            std::vector<std::pair<Mask,Mask>> replacement(removedCount);
            for (int v = 0; v < m; ++v) {
                if (solver.color[v] < 0) continue;
                auto &[a,b] = replacement[solver.color[v]];
                a |= 1u << need[v].row;
                b |= 1u << need[v].col;
            }
            for (auto [a,b] : replacement) std::cout << a << ' ' << b << '\n';
            return 0;
        }
        ++windows;
        total += solver.nodes;
        largest = std::max(largest, solver.nodes);
    }
    std::cout << "EXCLUDED " << removedCount << ' ' << windows << ' ' << total << ' ' << largest << '\n';
}
