// Exact covers by the maximum-area rectangles of the projective-plane board.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Plane = std::uint32_t;
struct Set {
    std::array<Word, 3> w{};
    Set operator&(Set b) const {
        return {{w[0] & b.w[0], w[1] & b.w[1], w[2] & b.w[2]}};
    }
    Set operator|(Set b) const {
        return {{w[0] | b.w[0], w[1] | b.w[1], w[2] | b.w[2]}};
    }
    Set minus(Set b) const {
        return {{w[0] & ~b.w[0], w[1] & ~b.w[1], w[2] & ~b.w[2]}};
    }
    bool within(Set b) const {
        return !(w[0] & ~b.w[0]) && !(w[1] & ~b.w[1]) && !(w[2] & ~b.w[2]);
    }
    bool empty() const {
        return !(w[0] | w[1] | w[2]);
    }
    int size() const {
        return std::popcount(w[0]) + std::popcount(w[1]) + std::popcount(w[2]);
    }
    void add(int j) {
        w[j / 64] |= Word{1} << (j % 64);
    }
    template <class F> void each(F visit) const {
        for (int i = 0; i < 3; ++i)
            for (Word x = w[i]; x; x &= x - 1)
                visit(i * 64 + std::countr_zero(x));
    }
};
struct Box {
    Plane rows, cols;
};
struct Label {
    Set incident;
    std::vector<std::pair<int, unsigned>> local;
    std::array<unsigned char, 65536> minimum;
    std::vector<Set> triples;
    std::array<std::array<unsigned, 128>, 3> chunks{};
};
struct Solver {
    std::array<Plane, 21> rows{}, cols{};
    std::array<Box, 168> boxes{};
    std::array<Label, 42> labels{};
    std::array<std::array<Set, 21>, 21> postings{};
    Set all, solution;
    int budget;
    bool minFour;
    std::array<Plane, 21> initialRows{}, initialCols{};
    Word states = 0;
    static unsigned compress(Plane m, Plane domain) {
        unsigned out = 0, bit = 1;
        for (Plane v = domain; v; v &= v - 1, bit <<= 1)
            if (m & (v & -v))
                out |= bit;
        return out;
    }
    void prepare() {
        for (int r = 0; r < 21; ++r) {
            if (!(std::cin >> rows[r]) || rows[r] >= (1u << 21) || std::popcount(rows[r]) != 16)
                throw std::runtime_error("Invalid board");
            for (int c = 0; c < 21; ++c)
                if (rows[r] >> c & 1)
                    cols[c] |= 1u << r;
        }
        for (int j = 0; j < 168; ++j) {
            auto &b = boxes[j];
            if (!(std::cin >> b.rows >> b.cols) || b.rows >= (1u << 21) || b.cols >= (1u << 21) ||
                std::popcount(b.rows) != 6 || std::popcount(b.cols) != 6)
                throw std::runtime_error("Invalid six by six box");
            for (int i = 0; i < j; ++i)
                if (boxes[i].rows == b.rows && boxes[i].cols == b.cols)
                    throw std::runtime_error("Repeated box");
            all.add(j);
            for (int i = 0; i < 21; ++i) {
                if (b.rows >> i & 1) {
                    if (b.cols & ~rows[i])
                        throw std::runtime_error("Forbidden cell");
                    for (int c = 0; c < 21; ++c)
                        if (b.cols >> c & 1)
                            postings[i][c].add(j);
                    labels[i].incident.add(j);
                    labels[i].local.emplace_back(j, compress(b.cols, rows[i]));
                }
                if (b.cols >> i & 1) {
                    labels[i + 21].incident.add(j);
                    labels[i + 21].local.emplace_back(j, compress(b.rows, cols[i]));
                }
            }
        }
        for (int site = 0; site < 42; ++site) {
            Label &l = labels[site];
            Plane domain = site < 21 ? rows[site] : cols[site - 21];
            for (int k = 0; k < 3; ++k)
                for (unsigned v = 0; v < 128; ++v)
                    l.chunks[k][v] = compress(v << (7 * k), domain);
            if (l.local.size() != 48)
                throw std::runtime_error("Wrong pencil size");
            // At one label, solve cover for every subset of its sixteen zero cells.
            // The recurrence ignores restrictions elsewhere and is a lower bound.
            l.minimum[0] = 0;
            for (unsigned target = 1; target < 65536; ++target) {
                int best = 16;
                for (auto [id, m] : l.local)
                    if (target & m)
                        best = std::min(best, 1 + l.minimum[target & ~m]);
                l.minimum[target] = best;
            }
            for (unsigned i = 0; i < 48; ++i)
                for (unsigned j = 0; j < i; ++j)
                    for (unsigned k = 0; k < j; ++k)
                        if ((l.local[i].second | l.local[j].second | l.local[k].second) == 65535) {
                            Set t;
                            t.add(l.local[i].first);
                            t.add(l.local[j].first);
                            t.add(l.local[k].first);
                            l.triples.push_back(t);
                        }
            if (l.triples.size() != 96)
                throw std::runtime_error("Wrong triple count");
        }
    }

    bool search(Set selected, Set allowed) {
        ++states;
        int used = selected.size(), left = budget - used;
        if (left < 0)
            return false;
        std::array<Plane, 21> covered = initialRows, columnCovered = initialCols;
        selected.each([&](int j) {
            const Box b = boxes[j];
            for (Plane v = b.rows; v; v &= v - 1)
                covered[std::countr_zero(v)] |= b.cols;
            for (Plane v = b.cols; v; v &= v - 1)
                columnCovered[std::countr_zero(v)] |= b.rows;
        });
        std::array<int, 42> degree{}, needed{};
        int sums[2]{};
        for (int i = 0; i < 42; ++i) {
            const Label &l = labels[i];
            Set here = selected & l.incident;
            degree[i] = here.size();
            Plane board = i < 21 ? rows[i] : cols[i - 21],
                  seen = i < 21 ? covered[i] : columnCovered[i - 21];
            Plane remaining = board & ~seen;
            unsigned compact = l.chunks[0][remaining & 127] | l.chunks[1][(remaining >> 7) & 127] |
                               l.chunks[2][remaining >> 14];
            int d = degree[i] + l.minimum[compact];
            if (d <= 3 && (i < 21 ? initialRows[i] : initialCols[i - 21]) == 0) {
                if (minFour || std::none_of(l.triples.begin(), l.triples.end(), [&](Set t) {
                        return here.within(t) && t.within(allowed);
                    }))
                    d = 4;
            }
            if (d - degree[i] > left)
                return false;
            needed[i] = d;
            sums[i / 21] += d;
        }
        // Each future rectangle contributes six memberships on each side.
        // Reserve the minima at the other twenty labels before restricting this one.
        if (sums[0] > 6 * budget || sums[1] > 6 * budget)
            return false;
        for (int i = 0; i < 42; ++i) {
            int maximum = needed[i] + 6 * budget - sums[i / 21];
            if (degree[i] > maximum)
                return false;
            if (degree[i] == maximum)
                allowed = allowed.minus(labels[i].incident.minus(selected));
            if (left && needed[i] - degree[i] == left)
                allowed = (allowed & labels[i].incident) | selected;
        }
        Set pivot;
        int width = 169;
        Set forced;
        for (int r = 0; r < 21; ++r)
            for (Plane v = rows[r] & ~covered[r]; v; v &= v - 1) {
                Set choices = postings[r][std::countr_zero(v)] & allowed;
                int n = choices.size();
                if (n == 0 || left == 0)
                    return false;
                if (n == 1)
                    forced = forced | choices;
                if (n < width) {
                    pivot = choices;
                    width = n;
                }
            }
        if (width == 169) {
            // A cover already suffices for the stated budget. Its witness is
            // checked against the original board by the caller.
            solution = selected;
            return true;
        }
        if (!forced.empty())
            return search(selected | forced, allowed);
        // The first chosen member of this list partitions the completions.
        std::vector<std::pair<int, int>> order;
        pivot.each([&](int j) {
            int gain = 0;
            for (Plane v = boxes[j].rows; v; v &= v - 1)
                gain += std::popcount(boxes[j].cols & ~covered[std::countr_zero(v)]);
            order.emplace_back(-gain, j);
        });
        std::sort(order.begin(), order.end());
        for (auto [priority, j] : order) {
            Set one;
            one.add(j);
            if (search(selected | one, allowed))
                return true;
            allowed = allowed.minus(one);
        }
        return false;
    }
    void run() {
        prepare();
        int mode, exactLabel, n;
        while (std::cin >> budget >> mode >> exactLabel >> n) {
            if (budget < 1 || budget > 21 || (mode != 0 && mode != 1) || n < 0 || n > 168 ||
                exactLabel < -1 || exactLabel >= 42)
                throw std::runtime_error("Bad root");
            minFour = mode;
            Set start;
            for (int i = 0; i < n; ++i) {
                int j;
                if (!(std::cin >> j) || j < 0 || j >= 168)
                    throw std::runtime_error("Bad root rectangle");
                start.add(j);
            }
            if (start.size() != n)
                throw std::runtime_error("Duplicate root");
            initialCols.fill(0);
            for (int i = 0; i < 21; ++i) {
                if (!(std::cin >> initialRows[i]) || (initialRows[i] & ~rows[i]))
                    throw std::runtime_error("Illegal initial coverage");
                for (Plane v = initialRows[i]; v; v &= v - 1)
                    initialCols[std::countr_zero(v)] |= 1u << i;
            }
            Set allowed =
                exactLabel < 0 ? all : all.minus(labels[exactLabel].incident.minus(start));
            states = 0;
            solution = {};
            bool found = search(start, allowed);
            std::cout << (found ? "COVER" : "EXCLUDED") << ' ' << states;
            if (found)
                solution.each([&](int j) { std::cout << ' ' << j; });
            std::cout << std::endl;
        }
    }
};
int main() {
    try {
        static Solver solver;
        solver.run();
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
