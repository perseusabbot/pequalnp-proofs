// Independent completion check. Each choice enlarges a Cartesian product and covers its entire
// hull.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
using W = std::uint64_t;
using Mask = std::array<W, 6>;
static void check(bool ok, const char *m) {
    if (!ok)
        throw std::runtime_error(m);
}
static void add(Mask &m, int j) {
    m[j / 64] |= W{1} << (j % 64);
}
static void drop(Mask &m, int j) {
    m[j / 64] &= ~(W{1} << (j % 64));
}
static bool in(const Mask &m, int j) {
    return (m[j / 64] >> (j % 64)) & 1;
}
static int last(Mask &m) {
    for (int i = 5; i >= 0; --i)
        if (m[i]) {
            int j = 63 - std::countl_zero(m[i]);
            m[i] ^= W{1} << j;
            return i * 64 + j;
        }
    return -1;
}
static Mask meet(Mask a, const Mask &b) {
    for (int i = 0; i < 6; ++i)
        a[i] &= b[i];
    return a;
}
static int size(const Mask &a) {
    int n = 0;
    for (auto v : a)
        n += std::popcount(v);
    return n;
}
struct Plane {
    std::array<unsigned, 21> rows{};
    std::array<std::array<int, 2>, 336> coords{};
    std::array<std::array<int, 21>, 21> index{};
    std::array<Mask, 336> edge{};
    std::vector<std::array<unsigned, 2>> six;
    explicit Plane(const char *path) {
        std::ifstream in(path);
        for (auto &r : rows)
            check(bool(in >> r) && std::popcount(r) == 16, "Invalid zero row");
        int n = 0;
        for (int q = 0; q < 21; ++q)
            for (int p = 0; p < 21; ++p)
                if (rows[p] >> q & 1) {
                    coords[n] = {p, q};
                    index[p][q] = n++;
                }
        check(n == 336, "Wrong number of zeros");
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < i; ++j) {
                auto [r, c] = coords[i];
                auto [p, q] = coords[j];
                if (!(rows[p] >> c & 1) || !(rows[r] >> q & 1)) {
                    add(edge[i], j);
                    add(edge[j], i);
                }
            }
        for (unsigned r = 0; r < (1u << 21); ++r)
            if (std::popcount(r) == 6) {
                unsigned columns = (1u << 21) - 1;
                for (unsigned a = r; a; a &= a - 1)
                    columns &= rows[std::countr_zero(a)];
                for (unsigned b = columns; b; b = (b - 1) & columns)
                    if (std::popcount(b) == 6)
                        six.push_back({r, b});
            }
        std::sort(six.begin(), six.end());
        check(six.size() == 168, "Wrong six-rectangle inventory");
    }
    bool clique(Mask eligible, int k, std::vector<int> &chosen) const {
        if (!k)
            return true;
        while (size(eligible) >= k) {
            int v = last(eligible);
            if (clique(meet(eligible, edge[v]), k - 1, chosen)) {
                chosen.push_back(v);
                return true;
            }
        }
        return false;
    }
};
template <int K> struct Hulls {
    struct State {
        Mask todo{};
        std::array<Mask, K> forbidden{};
        std::array<unsigned, K> rows{}, cols{};
    };
    const Plane &p;
    W nodes = 0;
    std::array<std::array<unsigned, 2>, K> solution{};
    bool put(State &s, int v, int color) const {
        if (!in(s.todo, v))
            return true;
        if (in(s.forbidden[color], v))
            return false;
        auto [r, c] = p.coords[v];
        auto &a = s.rows[color];
        auto &b = s.cols[color];
        drop(s.todo, v);
        if (!(a >> r & 1))
            for (unsigned t = b; t; t &= t - 1)
                drop(s.todo, p.index[r][std::countr_zero(t)]);
        if (!(b >> c & 1))
            for (unsigned t = a; t; t &= t - 1)
                drop(s.todo, p.index[std::countr_zero(t)][c]);
        a |= 1u << r;
        b |= 1u << c;
        for (int j = 0; j < 6; ++j)
            s.forbidden[color][j] |= p.edge[v][j];
        return true;
    }
    bool descend(State &s) {
        ++nodes;
        while (true) {
            Mask forced{}, pairs{}, many{};
            bool empty = true;
            for (int j = 0; j < 6; ++j)
                if (s.todo[j]) {
                    empty = false;
                    W seen = 0, twice = 0, three = 0;
                    for (auto &b : s.forbidden) {
                        W avail = s.todo[j] & ~b[j];
                        three |= twice & avail;
                        twice |= seen & avail;
                        seen |= avail;
                    }
                    if (seen != s.todo[j])
                        return false;
                    forced[j] = seen & ~twice;
                    pairs[j] = twice & ~three;
                    many[j] = three;
                }
            if (empty) {
                for (int c = 0; c < K; ++c)
                    solution[c] = {s.rows[c], s.cols[c]};
                return true;
            }
            if (size(forced)) {
                for (int v = last(forced); v >= 0; v = last(forced))
                    if (in(s.todo, v)) {
                        int c = 0;
                        while (c < K && in(s.forbidden[c], v))
                            ++c;
                        if (c == K || !put(s, v, c))
                            return false;
                    }
                continue;
            }
            Mask trial = size(pairs) ? pairs : many;
            int pivot = -1, best = 100000;
            for (int v = last(trial); v >= 0; v = last(trial)) {
                int options = 0;
                for (auto &b : s.forbidden)
                    options += !in(b, v);
                int score = 512 * options - size(meet(s.todo, p.edge[v]));
                if (score < best) {
                    pivot = v;
                    best = score;
                }
            }
            bool newColor = false;
            for (int c = K - 1; c >= 0; --c)
                if (!in(s.forbidden[c], pivot)) {
                    if (!s.rows[c]) {
                        if (newColor)
                            continue;
                        newColor = true;
                    }
                    State next = s;
                    check(put(next, pivot, c), "Invalid hull extension");
                    if (descend(next))
                        return true;
                }
            return false;
        }
    }
    bool cover(Mask target) {
        State s{};
        s.todo = target;
        std::vector<int> set;
        for (int k = std::min(7, K); k > 0; --k)
            if (p.clique(target, k, set))
                break;
        for (int i = 0; i < int(set.size()); ++i)
            check(put(s, set[i], i), "Invalid incompatible anchors");
        return descend(s);
    }
};
template <int K>
void solve(const Plane &p, const std::array<unsigned, 21> &missing, int id, bool control = false) {
    Mask target{};
    for (int i = 0; i < 336; ++i) {
        auto [r, c] = p.coords[i];
        if (missing[r] >> c & 1)
            add(target, i);
    }
    Hulls<K> h{p};
    if (h.cover(target)) {
        std::array<unsigned, 21> extra{};
        for (auto [a, b] : h.solution)
            for (unsigned t = a; t; t &= t - 1) {
                int r = std::countr_zero(t);
                check(!(b & ~p.rows[r]), "Illegal positive hull");
                extra[r] |= b;
            }
        for (int r = 0; r < 21; ++r)
            check(!(missing[r] & ~extra[r]), "Incomplete positive hull");
        std::cout << "COVER " << (control ? h.nodes : W(id));
        for (auto [a, b] : h.solution)
            std::cout << " " << a << " " << b;
        std::cout << std::endl;
        return;
    }
    if (control)
        std::cout << "EXCLUDED " << h.nodes << '\n';
    else
        std::cout << "EXCLUDED " << id << " " << size(target) << " " << h.nodes << std::endl;
}
int main(int argc, char **argv) {
    try {
        check(argc == 2 || argc == 7 || argc == 8,
              "Usage: hulls board [seeds fixed start stop stride [budget]]");
        Plane p(argv[1]);
        if (argc == 2) {
            int k;
            while (std::cin >> k) {
                std::array<unsigned, 21> rows{};
                for (int i = 0; i < 21; ++i)
                    check(bool(std::cin >> rows[i]) && !(rows[i] & ~p.rows[i]), "Invalid test board");
                switch (k) {
                case 4: solve<4>(p, rows, 0, true); break;
                case 5: solve<5>(p, rows, 0, true); break;
                case 6: solve<6>(p, rows, 0, true); break;
                case 7: solve<7>(p, rows, 0, true); break;
                case 8: solve<8>(p, rows, 0, true); break;
                case 9: solve<9>(p, rows, 0, true); break;
                default: throw std::runtime_error("Unsupported control budget");
                }
            }
            return 0;
        }
        std::ifstream input(argv[2]);
        int budget = argc == 8 ? std::stoi(argv[7]) : 13;
        int f = std::stoi(argv[3]), lo = std::stoi(argv[4]), hi = std::stoi(argv[5]),
            step = std::stoi(argv[6]);
        check((f == 4 || f == 5 || f == 6) && step > 0, "Unsupported independent search");
        check(budget == 13 || (budget == 14 && f >= 5), "Unsupported total budget");
        for (int i = 0; i < hi; ++i) {
            std::vector<int> ids(f);
            if (!(input >> ids[0]))
                break;
            for (int j = 1; j < f; ++j)
                check(bool(input >> ids[j]), "Missing seed");
            int weight;
            check(bool(input >> weight), "Missing orbit weight");
            if (i < lo || (i - lo) % step)
                continue;
            auto missing = p.rows;
            for (int j : ids) {
                check(j >= 0 && j < int(p.six.size()), "Invalid fixed rectangle");
                auto [a, b] = p.six[j];
                for (unsigned t = a; t; t &= t - 1)
                    missing[std::countr_zero(t)] &= ~b;
            }
            switch (budget - f) {
            case 7: solve<7>(p, missing, i); break;
            case 8: solve<8>(p, missing, i); break;
            case 9: solve<9>(p, missing, i); break;
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
