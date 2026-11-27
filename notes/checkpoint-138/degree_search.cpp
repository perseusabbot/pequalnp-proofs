// Exact cover by the 168 maximum rectangles, using point and line degree profiles.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Mask = std::uint32_t;
using Word = std::uint64_t;
constexpr int labels = 42;
using Degrees = std::array<unsigned char, labels>;
using Packed = std::array<Word, 6>;

struct Family {
    Word a[3]{};
    void add(int j) {
        a[j / 64] |= Word{1} << (j % 64);
    }
    int size() const {
        return std::popcount(a[0]) + std::popcount(a[1]) + std::popcount(a[2]);
    }
    Family operator&(Family y) const {
        return {a[0] & y.a[0], a[1] & y.a[1], a[2] & y.a[2]};
    }
    Family operator|(Family y) const {
        return {a[0] | y.a[0], a[1] | y.a[1], a[2] | y.a[2]};
    }
    Family minus(Family y) const {
        return {a[0] & ~y.a[0], a[1] & ~y.a[1], a[2] & ~y.a[2]};
    }
    bool subset(Family y) const {
        return !(a[0] & ~y.a[0]) && !(a[1] & ~y.a[1]) && !(a[2] & ~y.a[2]);
    }
    template <class F> void each(F f) const {
        for (int i = 0; i < 3; ++i)
            for (Word w = a[i]; w; w &= w - 1)
                f(64 * i + std::countr_zero(w));
    }
};
struct Box {
    Mask axes[2];
};
struct Site {
    Mask zeros = 0;
    Family through;
    std::array<Family, 16> cells{};
    std::vector<std::pair<int, unsigned>> local;
    std::array<unsigned char, 65536> min{};
    std::array<Family, 65536> one{};
    std::array<int, 5> opposite{};
};
struct State {
    Family selected, available;
    Degrees degree{};
    std::array<unsigned short, labels> missing{};
    unsigned left = 0;
};
struct Profile {
    Degrees value;
    Packed packed;
};
struct Search {
    std::array<Site, labels> site{};
    std::array<Box, 168> boxes{};
    std::array<std::array<int, 12>, 168> memberships{};
    std::array<std::array<unsigned short, 12>, 168> localCover{};
    std::array<Mask, 21> forbidden{};
    std::vector<Mask> parityMasks;
    std::array<std::vector<Family>, labels> triples;
    std::vector<Profile> profiles;
    Family all, answer;
    int budget, minimum;
    int surplus = -1;
    Word states = 0;
    static unsigned compact(Mask w, Mask domain) {
        unsigned out = 0;
        for (unsigned j = 0; domain; domain &= domain - 1, ++j)
            if (w & (domain & -domain))
                out |= 1u << j;
        return out;
    }
    static Packed pack(const Degrees &d) {
        Packed p{};
        for (int i = 0; i < labels; ++i)
            p[i / 8] |= Word(d[i]) << ((i % 8) * 8);
        return p;
    }
    static bool enough(const Packed &p, const Packed &lower) {
        // The high bit prevents any borrow across byte boundaries.
        constexpr Word high = 0x8080808080808080ULL;
        for (int i = 0; i < 6; ++i)
            if ((((p[i] | high) - lower[i]) & high) != high)
                return false;
        return true;
    }
    void board() {
        constexpr Mask full = (1u << 21) - 1;
        for (int i = 0; i < 21; ++i) {
            Mask w;
            if (!(std::cin >> w) || w > full || std::popcount(w) != 16)
                throw std::runtime_error("Board row");
            site[i].zeros = w;
            for (Mask v = w; v; v &= v - 1)
                site[21 + std::countr_zero(v)].zeros |= 1u << i;
        }
        for (int i = 0; i < labels; ++i) {
            Mask v = full ^ site[i].zeros;
            if (std::popcount(v) != 5)
                throw std::runtime_error("Board column");
            if (i < 21)
                forbidden[i] = v;
            int k = 0;
            for (; v; v &= v - 1)
                site[i].opposite[k++] = (i < 21 ? 21 : 0) + std::countr_zero(v);
        }
        for (int j = 0; j < 168; ++j) {
            auto &b = boxes[j];
            if (!(std::cin >> b.axes[0] >> b.axes[1]))
                throw std::runtime_error("Missing rectangle");
            for (int t = 0; t < j; ++t)
                if (boxes[t].axes[0] == b.axes[0] && boxes[t].axes[1] == b.axes[1])
                    throw std::runtime_error("Duplicate rectangle");
            int k = 0;
            all.add(j);
            for (int side = 0; side < 2; ++side) {
                Mask a = b.axes[side], other = b.axes[1 - side];
                if (a > full || std::popcount(a) != 6)
                    throw std::runtime_error("Box dimension");
                for (int i = 0; i < 21; ++i) {
                    int label = side * 21 + i;
                    auto &l = site[label];
                    if (2 * ((a >> i) & 1) + std::popcount(other & (full ^ l.zeros)) != 2)
                        throw std::runtime_error("Unbalanced rectangle");
                    if (!(a >> i & 1))
                        continue;
                    if (other & ~l.zeros)
                        throw std::runtime_error("Forbidden cell");
                    unsigned w = compact(other, l.zeros);
                    memberships[j][k] = label;
                    localCover[j][k++] = w;
                    l.through.add(j);
                    l.local.emplace_back(j, w);
                    for (unsigned v = w; v; v &= v - 1)
                        l.cells[std::countr_zero(v)].add(j);
                }
            }
        }
        for (auto &l : site) {
            l.one[0] = l.through;
            l.min[0] = 0;
            for (unsigned m = 1; m < 65536; ++m) {
                l.one[m] = l.one[m & (m - 1)] & l.cells[std::countr_zero(m)];
                int n = 17;
                for (auto [j, w] : l.local)
                    if (w & m)
                        n = std::min(n, 1 + l.min[m & ~w]);
                l.min[m] = n;
            }
        }
        // Binary elimination for all point sets meeting every line evenly.
        std::array<Mask, 21> basis{}, combination{};
        parityMasks = {0};
        for (int i = 0; i < 21; ++i) {
            Mask x = forbidden[i], coeff = 1u << i;
            while (x) {
                int pivot = std::bit_width(x) - 1;
                if (!basis[pivot]) {
                    basis[pivot] = x;
                    combination[pivot] = coeff;
                    break;
                }
                x ^= basis[pivot];
                coeff ^= combination[pivot];
            }
            if (!x) {
                auto n = parityMasks.size();
                for (unsigned j = 0; j < n; ++j)
                    parityMasks.push_back(parityMasks[j] ^ coeff);
            }
        }
        if (parityMasks.size() != 2048)
            throw std::runtime_error("Wrong parity code");
    }
    void select(State &n, int j) const {
        Family one;
        one.add(j);
        n.available = n.available.minus(one);
        n.selected.add(j);
        --n.left;
        for (int k = 0; k < 12; ++k) {
            int i = memberships[j][k];
            ++n.degree[i];
            n.missing[i] &= ~localCover[j][k];
        }
    }
    bool requirements(const State &n, Degrees &need) const {
        int sums[2]{};
        for (int i = 0; i < labels; ++i) {
            auto &l = site[i];
            auto m = n.missing[i];
            int extra = l.min[m];
            if (extra == 1 && !(l.one[m] & n.available).size())
                extra = 2;
            int d = std::max(minimum, n.degree[i] + extra);
            if (d == 3 && !triples[i].empty()) {
                Family here = n.selected & l.through, possible = n.available | here;
                if (std::none_of(triples[i].begin(), triples[i].end(),
                                 [&](Family t) { return here.subset(t) && t.subset(possible); }))
                    ++d;
            }
            if (d > n.degree[i] + int(n.left))
                return false;
            need[i] = d;
            sums[i / 21] += d;
        }
        return sums[0] <= 6 * budget && sums[1] <= 6 * budget;
    }
    void place(Degrees &d, const Degrees &lower, int units, int first) {
        if (!units) {
            if (surplus >= 0) {
                for (int i = 0; i < labels; ++i)
                    if (d[i] != 4 + ((boxes[surplus].axes[i / 21] >> (i % 21)) & 1))
                        return;
            }
            profiles.push_back({d, pack(d)});
            return;
        }
        for (int i = first; i < 21; ++i) {
            const auto &lines = site[i].opposite;
            if (d[i] + 2 > budget ||
                std::any_of(lines.begin(), lines.end(), [&](int j) { return d[j] <= lower[j]; }))
                continue;
            d[i] += 2;
            for (int j : lines)
                --d[j];
            place(d, lower, units - 1, i);
            d[i] -= 2;
            for (int j : lines)
                ++d[j];
        }
    }
    void makeProfiles(const Degrees &lower) {
        profiles.clear();
        for (Mask parity : parityMasks) {
            Degrees d{};
            int extra = 6 * budget;
            for (int i = 0; i < 21; ++i) {
                d[i] = lower[i] + ((lower[i] ^ (parity >> i)) & 1);
                extra -= d[i];
            }
            if (extra < 0 || (extra & 1) || *std::max_element(d.begin(), d.begin() + 21) > budget)
                continue;
            bool valid = true;
            for (int j = 21; j < 42; ++j) {
                int s = 0;
                for (int i : site[j].opposite)
                    s += d[i];
                if (s % 2)
                    throw std::runtime_error("Invalid parity vector");
                int value = budget - s / 2;
                if (value < lower[j]) {
                    valid = false;
                    break;
                }
                d[j] = value;
            }
            if (valid)
                place(d, lower, extra / 2, 0);
        }
    }
    bool solve(State n, const std::vector<int> &parent) {
        ++states;
        Degrees need;
        if (!requirements(n, need))
            return false;
        auto lower = pack(need);
        Degrees hi{}, lo;
        lo.fill(127);
        std::vector<int> alive;
        for (int k : parent) {
            const auto &p = profiles[k];
            if (!enough(p.packed, lower))
                continue;
            alive.push_back(k);
            for (int i = 0; i < labels; ++i) {
                hi[i] = std::max(hi[i], p.value[i]);
                lo[i] = std::min(lo[i], p.value[i]);
            }
        }
        if (alive.empty())
            return false;
        for (int i = 0; i < labels; ++i) {
            if (hi[i] == n.degree[i])
                n.available = n.available.minus(site[i].through);
            if (n.left && lo[i] == n.degree[i] + n.left)
                n.available = n.available & site[i].through;
        }
        Family pivot, forced;
        int width = 169;
        for (int i = 0; i < 21; ++i)
            for (unsigned m = n.missing[i]; m; m &= m - 1) {
                auto allowed = n.available & site[i].cells[std::countr_zero(m)];
                int k = allowed.size();
                if (!k || !n.left)
                    return false;
                if (k == 1)
                    forced = forced | allowed;
                if (k < width) {
                    width = k;
                    pivot = allowed;
                }
            }
        if (width == 169) {
            if (!n.left || minimum == 0) {
                answer = n.selected;
                return true;
            }
            // For a prescribed degree profile, a completed board may still need padding.
            pivot = n.available;
            width = pivot.size();
        }
        if (forced.size()) {
            if (forced.size() > int(n.left))
                return false;
            forced.each([&](int j) { select(n, j); });
            return solve(n, alive);
        }
        // A label capped at degree three must finish with a local covering triple.
        int tight = -1;
        std::vector<Family> options;
        for (int i = 0; i < labels; ++i)
            if (hi[i] == 3 && n.degree[i] < 3 && !triples[i].empty()) {
                Family here = n.selected & site[i].through, available = here | n.available;
                std::vector<Family> feasible;
                for (auto t : triples[i])
                    if (here.subset(t) && t.subset(available)) {
                        feasible.push_back(t.minus(here));
                        if (int(feasible.size()) >= width)
                            break;
                    }
                if (feasible.empty())
                    return false;
                if (int(feasible.size()) < width) {
                    width = feasible.size();
                    tight = i;
                    options = std::move(feasible);
                }
            }
        if (tight >= 0) {
            for (auto t : options) {
                if (t.size() > int(n.left))
                    continue;
                State child = n;
                t.each([&](int j) { select(child, j); });
                child.available = child.available.minus(site[tight].through);
                if (solve(child, alive))
                    return true;
            }
            return false;
        }
        bool found = false;
        pivot.each([&](int j) {
            if (found)
                return;
            State child = n;
            select(child, j);
            found = solve(child, alive);
            Family one;
            one.add(j);
            n.available = n.available.minus(one);
        });
        return found;
    }
    void run() {
        board();
        int hole, exact, count;
        while (std::cin >> budget >> minimum >> hole >> exact >> count) {
            if (!(std::cin >> surplus) || surplus < -1 || surplus >= 168 ||
                (surplus >= 0 && (budget != 15 || minimum != 4)))
                throw std::runtime_error("Wrong surplus profile");
            if (budget < 1 || budget > 21 || minimum < 0 || minimum > 6 || hole < -1 ||
                hole >= 441 || exact < -1 || exact >= 42 || count < 0 || count > budget)
                throw std::runtime_error("Invalid root");
            State n{};
            n.left = budget;
            n.available = all;
            std::vector<int> seed(count);
            for (auto &j : seed)
                if (!(std::cin >> j) || j < 0 || j >= 168)
                    throw std::runtime_error("Wrong seed");
            std::array<Mask, 42> pre{};
            for (int i = 0; i < 21; ++i) {
                if (!(std::cin >> pre[i]) || (pre[i] & ~site[i].zeros))
                    throw std::runtime_error("Invalid prefill");
                for (Mask v = pre[i]; v; v &= v - 1)
                    pre[21 + std::countr_zero(v)] |= 1u << i;
            }
            if (hole >= 0) {
                const int r = hole / 21, c = hole % 21;
                if (!(pre[r] >> c & 1))
                    throw std::runtime_error("Missing hole prefill");
                n.available = n.available.minus(site[r].through & site[21 + c].through);
            }
            for (int i = 0; i < labels; ++i) {
                auto &l = site[i];
                int target = compact(l.zeros & ~pre[i], l.zeros);
                n.missing[i] = target;
                auto &ts = triples[i];
                ts.clear();
                if (minimum > 3 || l.min[target] != 3)
                    continue;
                for (unsigned a = 0; a < l.local.size(); ++a)
                    for (unsigned b = 0; b < a; ++b)
                        for (unsigned c = 0; c < b; ++c) {
                            auto [i1, s1] = l.local[a];
                            auto [i2, s2] = l.local[b];
                            auto [i3, s3] = l.local[c];
                            if (target & ~(s1 | s2 | s3))
                                continue;
                            Family t;
                            t.add(i1);
                            t.add(i2);
                            t.add(i3);
                            if (t.subset(n.available))
                                ts.push_back(t);
                        }
            }
            bool possible = true;
            for (int j : seed) {
                Family one;
                one.add(j);
                if (!one.subset(n.available)) {
                    possible = false;
                    break;
                }
                select(n, j);
            }
            if (exact >= 0)
                n.available = n.available.minus(site[exact].through);
            states = 0;
            profiles.clear();
            answer = {};
            Degrees lower;
            if (possible && requirements(n, lower)) {
                makeProfiles(lower);
                std::vector<int> ids;
                for (unsigned j = 0; j < profiles.size(); ++j)
                    ids.push_back(j);
                possible = solve(n, ids);
            } else
                possible = false;
            std::cout << (possible ? "COVER" : "EXCLUDED") << ' ' << states << ' '
                      << profiles.size();
            if (possible)
                answer.each([&](int j) { std::cout << ' ' << j; });
            std::cout << std::endl;
        }
    }
};
int main() {
    try {
        static Search s;
        s.run();
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
