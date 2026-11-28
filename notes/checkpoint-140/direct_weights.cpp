// Independent integer verifier. Generate maximal rectangles by exhausting every row subset.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using W = std::uint64_t;
using Perm = std::array<unsigned char, 42>;
using Weights = std::array<int, 336>;
void check(bool yes, const char *message) {
    if (!yes)
        throw std::runtime_error(message);
}
struct PermHash {
    std::size_t operator()(const Perm &g) const {
        W h = 14695981039346656037ULL;
        for (auto v : g)
            h = (h ^ v) * 1099511628211ULL;
        return h;
    }
};
struct Rectangle {
    unsigned rows, cols;
    std::vector<int> entries;
    W key() const {
        return rows | (W(cols) << 21);
    }
    int load(const Weights &w) const {
        int t = 0;
        for (int x : entries)
            t += w[x];
        return t;
    }
};
struct Direct {
    std::array<unsigned, 21> board{};
    std::array<std::array<int, 2>, 336> cells{};
    std::array<std::array<int, 21>, 21> cellIndex{};
    std::vector<Perm> group;
    std::vector<int> population;
    std::vector<Rectangle> maxima, others;
    std::unordered_map<W, int> maxIndex, otherIndex;
    std::unordered_map<int, std::vector<unsigned char>> cache;
    W nodes = 0, leaves = 0, splits = 0;
    int maxDepth = 0;
    explicit Direct(std::istream &input) {
        for (auto &r : board)
            check(bool(input >> r) && std::popcount(r) == 16 && r < (1u << 21),
                  "Invalid matrix row");
        int n = 0;
        for (int r = 0; r < 21; ++r)
            for (int c = 0; c < 21; ++c)
                if (board[r] >> c & 1) {
                    cells[n] = {r, c};
                    cellIndex[r][c] = n++;
                }
        check(n == 336, "Wrong matrix area");
        std::vector<unsigned> intersection(1u << 21);
        intersection[0] = (1u << 21) - 1;
        for (unsigned a = 1; a < intersection.size(); ++a) {
            unsigned b = intersection[a] = intersection[a & (a - 1)] & board[std::countr_zero(a)];
            if (!b)
                continue;
            unsigned closure = 0;
            for (int r = 0; r < 21; ++r)
                if ((board[r] & b) == b)
                    closure |= 1u << r;
            if (closure != a)
                continue;
            Rectangle box{a, b, {}};
            for (unsigned x = a; x; x &= x - 1)
                for (unsigned y = b; y; y &= y - 1)
                    box.entries.push_back(cellIndex[std::countr_zero(x)][std::countr_zero(y)]);
            if (box.entries.size() == 36) {
                check(std::popcount(a) == 6 && std::popcount(b) == 6, "Unexpected maximum shape");
                maxIndex[box.key()] = maxima.size();
                maxima.push_back(std::move(box));
            } else {
                check(box.entries.size() <= 28, "Unexpected exceptional area");
                otherIndex[box.key()] = others.size();
                others.push_back(std::move(box));
            }
        }
        check(maxima.size() == 168 && others.size() == 25067, "Inventory differs");
        int number;
        check(bool(input >> number) && number > 0 && number <= 10, "Invalid generators");
        std::vector<Perm> gens(number);
        for (auto &g : gens) {
            std::array<bool, 42> used{};
            for (auto &x : g) {
                int i;
                check(bool(input >> i) && i >= 0 && i < 42 && !used[i], "Invalid permutation");
                used[i] = true;
                x = i;
            }
            for (int r = 0; r < 21; ++r)
                for (int c = 0; c < 21; ++c) {
                    auto [p, q] = std::minmax(g[r], g[c + 21]);
                    check(p < 21 && q >= 21 &&
                              ((board[p] >> (q - 21)) & 1) == ((board[r] >> c) & 1),
                          "Generator changes the board");
                }
        }
        Perm id{};
        std::iota(id.begin(), id.end(), 0);
        group.reserve(241920);
        group.push_back(id);
        std::unordered_set<Perm, PermHash> seen{id};
        for (std::size_t j = 0; j < group.size(); ++j)
            for (const auto &g : gens) {
                Perm h{};
                for (int x = 0; x < 42; ++x)
                    h[x] = g[group[j][x]];
                if (seen.insert(h).second)
                    group.push_back(h);
            }
        check(group.size() == 241920, "Unexpected board group");
        population.resize(group.size());
        std::iota(population.begin(), population.end(), 0);
    }
    W image(int g, W original) const {
        W result = 0;
        for (W x = original; x; x &= x - 1)
            result |= W{1} << group[g][std::countr_zero(x)];
        return result;
    }
    int moveCell(int g, int x) const {
        auto [p, q] = cells[x];
        auto [a, b] = std::minmax(group[g][p], group[g][q + 21]);
        return cellIndex[a][b - 21];
    }
    const std::vector<unsigned char> &movedMaximum(int h) {
        auto [it, newEntry] = cache.try_emplace(h);
        if (newEntry) {
            it->second.reserve(group.size());
            for (int g : population)
                it->second.push_back(maxIndex.at(image(g, maxima[h].key())));
        }
        return it->second;
    }
    void visit(std::istream &proof, const std::array<bool, 336> &open,
               const std::vector<int> &allowed, const std::vector<int> &sym, int slots, int depth) {
        ++nodes;
        maxDepth = std::max(maxDepth, depth);
        Weights w{};
        for (int x = 0; x < 336; ++x)
            check(bool(proof >> w[x]) && w[x] >= 0 && w[x] <= 1000000 && (open[x] || !w[x]),
                  "Invalid weight or support");
        int branches;
        check(bool(proof >> branches) && branches >= 0 && branches <= 25067,
              "Invalid manifest of branches");
        W total = std::accumulate(w.begin(), w.end(), W{});
        check(total > 0 && slots > 0, "Invalid total");
        std::vector<int> loads(others.size()), owner(others.size(), -2);
        int heavy = 0;
        for (int j : allowed) {
            loads[j] = others[j].load(w);
            if (W(slots) * loads[j] >= total) {
                owner[j] = -1;
                ++heavy;
            }
        }
        if (!heavy) {
            check(branches == 0, "Redundant branches at a leaf");
            ++leaves;
            return;
        }
        ++splits;
        for (int g : sym)
            for (int x = 0; x < 336; ++x)
                check(w[x] == w[moveCell(g, x)], "Weights are not invariant");
        for (int child = 0; child < branches; ++child) {
            int e;
            check(bool(proof >> e) && e >= 0 && e < int(others.size()) && owner[e] == -1,
                  "Missing or ineligible child");
            std::vector<int> stabilizer;
            auto key = others[e].key();
            for (int g : sym) {
                W dest = image(g, key);
                int h = otherIndex.at(dest);
                check(owner[h] == -1 || owner[h] == child, "Marked orbits cross another class");
                if (owner[h] == -1) {
                    owner[h] = child;
                    --heavy;
                }
                if (dest == key)
                    stabilizer.push_back(g);
            }
            check(!stabilizer.empty(), "Lost the identity symmetry");
            auto nextOpen = open;
            Weights fresh = w;
            for (int x : others[e].entries) {
                nextOpen[x] = false;
                fresh[x] = 0;
            }
            auto freshTotal = std::accumulate(fresh.begin(), fresh.end(), std::int64_t{});
            std::int64_t need = freshTotal - std::int64_t(slots - 2) * loads[e];
            std::vector<int> possible;
            possible.reserve(allowed.size());
            for (int j : allowed)
                if (j != e && loads[j] <= loads[e] && (need <= 0 || others[j].load(fresh) >= need))
                    possible.push_back(j);
            visit(proof, nextOpen, possible, stabilizer, slots - 1, depth + 1);
        }
        check(!heavy, "An eligible heaviest rectangle was missed");
    }
    void stratum(std::istream &in) {
        int k, cap, roots;
        check(bool(in >> k >> cap >> roots) && k >= 0 && k <= 3 && (cap == 27 || cap == 28) &&
                  roots > 0,
              "Invalid stratum");
        W space = 1, expected = 1, actual = 0;
        for (int j = 1; j <= k; ++j) {
            space *= 168;
            expected = expected * (169 - j) / j;
        }
        std::vector<int> ownership(space, -1), allowed;
        for (int j = 0; j < int(others.size()); ++j)
            if (int(others[j].entries.size()) <= cap)
                allowed.push_back(j);
        nodes = leaves = splits = 0;
        maxDepth = 0;
        for (int z = 0; z < roots; ++z) {
            std::array<bool, 336> open;
            open.fill(true);
            auto sym = population;
            std::array<const std::vector<unsigned char> *, 3> moves{};
            int last = -1;
            for (int i = 0; i < k; ++i) {
                int h;
                check(bool(in >> h) && last < h && h < 168, "Invalid marked maximum");
                last = h;
                moves[i] = &movedMaximum(h);
                for (int x : maxima[h].entries)
                    open[x] = false;
                std::erase_if(sym, [&](int g) { return (*moves[i])[g] != h; });
            }
            for (int g : population) {
                std::array<unsigned char, 3> v{};
                for (int i = 0; i < k; ++i)
                    v[i] = (*moves[i])[g];
                std::sort(v.begin(), v.begin() + k);
                int id = 0;
                for (int i = 0; i < k; ++i)
                    id = id * 168 + v[i];
                if (ownership[id] < 0) {
                    ownership[id] = z;
                    ++actual;
                } else
                    check(ownership[id] == z, "Maximum orbits overlap");
            }
            visit(in, open, allowed, sym, 13 - k, 0);
        }
        check(actual == expected, "Maximum orbits do not exhaust their physical subsets");
        std::cout << k << " " << cap << " " << roots << " " << actual << " " << nodes << " "
                  << leaves << " " << splits << " " << maxDepth << "\n";
    }
};
int main(int argc, char **argv) {
    try {
        check(argc == 3, "Usage: direct_weights geometry certificate-stream");
        std::ifstream board(argv[1]), proof(argv[2]);
        Direct verify(board);
        int n;
        check(bool(proof >> n) && n >= 1, "Missing certificate strata");
        for (int i = 0; i < n; ++i)
            verify.stratum(proof);
        std::string extra;
        check(!(proof >> extra), "Trailing certificate records");
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
