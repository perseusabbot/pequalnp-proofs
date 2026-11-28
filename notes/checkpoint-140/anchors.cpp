// Normalize six maximum rectangles by their least four-subset orbit.
#include "common.hpp"
#include <limits>
#include <numeric>
#include <unordered_set>

struct HashPerm {
    std::size_t operator()(const Perm &p) const {
        Word h = 14695981039346656037ULL;
        for (auto v : p)
            h = (h ^ v) * 1099511628211ULL;
        return h;
    }
};
using Four = std::array<int, 4>;
struct Orbit {
    Four base;
    std::vector<int> stabilizer;
};
struct Quartets {
    int choose[169][5]{};
    std::vector<Perm> group, inverse;
    std::vector<Orbit> orbits;
    std::vector<std::uint16_t> type;
    std::vector<int> transporter;

    explicit Quartets(const Geometry &board) {
        Perm identity{};
        std::iota(identity.begin(), identity.end(), 0);
        group.push_back(identity);
        std::unordered_set<Perm, HashPerm> seen{identity};
        seen.reserve(250000);
        group.reserve(250000);
        for (std::size_t i = 0; i < group.size(); ++i)
            for (const auto &g : board.generators) {
                Perm next{};
                for (int j = 0; j < 168; ++j)
                    next[j] = g[group[i][j]];
                if (seen.insert(next).second)
                    group.push_back(next);
            }
        require(group.size() == 241920, "Group order differs");
        inverse.resize(group.size());
        for (std::size_t i = 0; i < group.size(); ++i)
            for (int j = 0; j < 168; ++j)
                inverse[i][group[i][j]] = j;
        for (int i = 0; i <= 168; ++i) {
            choose[i][0] = 1;
            for (int j = 1; j <= 4 && j <= i; ++j)
                choose[i][j] = choose[i - 1][j - 1] + choose[i - 1][j];
        }
        type.resize(choose[168][4], 65535);
        transporter.resize(type.size(), -1);
        Word physical = 0;
        for (int d = 3; d < 168; ++d)
            for (int c = 2; c < d; ++c)
                for (int b = 1; b < c; ++b)
                    for (int a = 0; a < b; ++a) {
                        int root = rank(a, b, c, d);
                        if (transporter[root] >= 0)
                            continue;
                        int id = orbits.size();
                        Orbit orbit{{a, b, c, d}, {}};
                        int mass = 0;
                        for (int i = 0; i < int(group.size()); ++i) {
                            const auto &g = group[i];
                            int r = rank(g[a], g[b], g[c], g[d]);
                            if (r == root)
                                orbit.stabilizer.push_back(i);
                            if (transporter[r] < 0) {
                                transporter[r] = i;
                                type[r] = id;
                                ++mass;
                            } else
                                require(type[r] == id, "Four-subset orbits intersect");
                        }
                        require(mass * orbit.stabilizer.size() == group.size(),
                                "Four-subset multiplicity differs");
                        physical += mass;
                        orbits.push_back(std::move(orbit));
                    }
        require(physical == type.size(), "A four-subset is missing");
    }
    int rank(int a, int b, int c, int d) const {
        if (a > b)
            std::swap(a, b);
        if (c > d)
            std::swap(c, d);
        if (a > c)
            std::swap(a, c);
        if (b > d)
            std::swap(b, d);
        if (b > c)
            std::swap(b, c);
        return a + choose[b][2] + choose[c][3] + choose[d][4];
    }
    template <class F> void fives(F emit) const {
        for (int id = 0; id < int(orbits.size()); ++id) {
            const auto &[base, stabilizer] = orbits[id];
            for (int x = 0; x < 168; ++x) {
                if (std::find(base.begin(), base.end(), x) != base.end())
                    continue;
                std::array<int, 5> v{base[0], base[1], base[2], base[3], x};
                int ways = 0;
                bool canonical = true;
                for (int a = 0; a < 5 && canonical; ++a) {
                    Four q{};
                    int n = 0;
                    for (int j = 0; j < 5; ++j)
                        if (j != a)
                            q[n++] = v[j];
                    int idx = rank(q[0], q[1], q[2], q[3]);
                    if (type[idx] < id) {
                        canonical = false;
                        break;
                    }
                    if (type[idx] > id)
                        continue;
                    int y = inverse[transporter[idx]][v[a]];
                    for (int h : stabilizer) {
                        int w = group[h][y];
                        if (w < x) {
                            canonical = false;
                            break;
                        }
                        ways += (w == x);
                    }
                }
                if (!canonical)
                    continue;
                require(ways > 0 && group.size() % ways == 0, "Five-subset stabilizer differs");
                std::sort(v.begin(), v.end());
                emit(v, group.size() / ways);
            }
        }
    }
    template <class F> void shortSets(int k, F emit) const {
        require(k >= 1 && k <= 3, "Unsupported small orbit size");
        auto rankSmall = [&](int a, int b, int c) {
            if (a > b)
                std::swap(a, b);
            if (b > c)
                std::swap(b, c);
            if (a > b)
                std::swap(a, b);
            if (k == 1)
                return c;
            if (k == 2)
                return b + choose[c][2];
            return a + choose[b][2] + choose[c][3];
        };
        std::vector<bool> marked(choose[168][k]);
        for (int c = 0; c < 168; ++c)
            for (int b = (k < 2 ? -1 : 0); b < (k < 2 ? 0 : c); ++b)
                for (int a = (k < 3 ? -1 : 0); a < (k < 3 ? 0 : b); ++a) {
                    int i = rankSmall(a, b, c);
                    if (marked[i])
                        continue;
                    int weight = 0;
                    for (const auto &g : group) {
                        int j = rankSmall(a < 0 ? -1 : g[a], b < 0 ? -1 : g[b], g[c]);
                        if (!marked[j]) {
                            marked[j] = true;
                            ++weight;
                        }
                    }
                    std::vector<int> v;
                    if (a >= 0)
                        v.push_back(a);
                    if (b >= 0)
                        v.push_back(b);
                    v.push_back(c);
                    emit(v, weight);
                }
    }
    template <class F> void sixes(F emit) const {
        for (int id = 0; id < int(orbits.size()); ++id) {
            const auto &[base, stab] = orbits[id];
            std::vector<int> vertices;
            for (int x = 0; x < 168; ++x) {
                if (std::find(base.begin(), base.end(), x) != base.end())
                    continue;
                bool ok = true;
                for (int i = 0; i < 4; ++i) {
                    Four q = base;
                    q[i] = x;
                    if (type[rank(q[0], q[1], q[2], q[3])] < id)
                        ok = false;
                }
                if (ok)
                    vertices.push_back(x);
            }
            for (std::size_t j = 0; j < vertices.size(); ++j)
                for (std::size_t k = j + 1; k < vertices.size(); ++k) {
                    int x = vertices[j], y = vertices[k], code = 168 * x + y;
                    std::array<int, 6> v{base[0], base[1], base[2], base[3], x, y};
                    int ways = 0;
                    bool canonical = true;
                    for (int a = 0; a < 6 && canonical; ++a)
                        for (int b = a + 1; b < 6 && canonical; ++b) {
                            Four q{};
                            int n = 0;
                            for (int z = 0; z < 6; ++z)
                                if (z != a && z != b)
                                    q[n++] = v[z];
                            int idx = rank(q[0], q[1], q[2], q[3]);
                            if (type[idx] < id) {
                                canonical = false;
                                break;
                            }
                            if (type[idx] > id)
                                continue;
                            const auto &back = inverse[transporter[idx]];
                            int va = back[v[a]], vb = back[v[b]];
                            for (int h : stab) {
                                int u = group[h][va], w = group[h][vb];
                                if (u > w)
                                    std::swap(u, w);
                                int image = 168 * u + w;
                                if (image < code) {
                                    canonical = false;
                                    break;
                                }
                                ways += (image == code);
                            }
                        }
                    if (!canonical)
                        continue;
                    require(ways > 0 && group.size() % ways == 0, "Six-subset stabilizer differs");
                    std::sort(v.begin(), v.end());
                    emit(v, group.size() / ways);
                }
        }
    }
};
int main(int argc, char **argv) {
    try {
        require(argc == 2 || argc == 3, "Usage: anchors board [size]");
        int k = argc == 2 ? 6 : std::stoi(argv[2]);
        require(k >= 1 && k <= 6, "Invalid anchor size");
        Quartets q{Geometry(argv[1])};
        Word count = 0, mass = 0;
        auto emit = [&](const auto &s, Word w) {
            for (auto x : s)
                std::cout << x << ' ';
            std::cout << w << '\n';
            ++count;
            mass += w;
        };
        if (k <= 3)
            q.shortSets(k, emit);
        if (k == 4)
            for (const auto &o : q.orbits)
                emit(o.base, q.group.size() / o.stabilizer.size());
        if (k == 5)
            q.fives(emit);
        if (k == 6)
            q.sixes(emit);
        Word expected = 1;
        for (int j = 1; j <= k; ++j)
            expected = expected * (169 - j) / j;
        require(mass == expected, "Orbit weights do not cover all subsets");
        std::cerr << count << " orbits of " << k << " rectangles, " << mass
                  << " physical subsets\n";
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
