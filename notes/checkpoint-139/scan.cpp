#include "complete.hpp"
#include "profiles.hpp"
#include <fstream>
#include <numeric>
#include <string>
#include <unordered_map>

struct Permutation {
    std::array<std::array<Word, 128>, 6> chunks{};
    Word operator()(Word x) const {
        Word out = 0;
        for (int k = 0; k < 6; ++k) {
            out |= chunks[k][x & 127];
            x >>= 7;
        }
        return out;
    }
};
struct Root {
    int a, b;
    std::vector<int> maps;
};
struct Ordinary {
    Box box;
    int rank;
};

struct Inventory {
    std::vector<Ordinary> members;
    std::vector<Permutation> maps;
    std::vector<Root> roots;
    std::unordered_map<Word, int> index;
    int groupOrder{};

    void read(const Board &board, std::istream &in) {
        int n;
        in >> n;
        check(n == 25067, "Wrong exceptional rectangle count");
        for (int i = 0; i < n; ++i) {
            Mask a, b;
            int rank;
            check(bool(in >> a >> b >> rank) && rank >= 0 && rank < 8, "Wrong exceptional input");
            Box box = board.box(a, b);
            check(i == 0 || members.back().box.key() < box.key(), "Exceptional input out of order");
            for (int s = 0; s < 2; ++s) {
                Mask common = full;
                for (Mask t = box.axes[s]; t; t &= t - 1)
                    common &= board.sites[21 * s + std::countr_zero(t)].zeros;
                check(common == box.axes[1 - s], "Exceptional rectangle fails maximality");
            }
            check(std::popcount(a) * std::popcount(b) <= 28, "Exceptional area exceeds 28");
            members.push_back({box, rank});
            index.emplace(box.key(), i);
        }
        int count;
        in >> groupOrder >> count;
        check(groupOrder == 241920 && count > 0 && count <= groupOrder, "Wrong board group");
        maps.resize(count);
        for (auto &perm : maps) {
            std::array<int, 42> g{};
            Word seen = 0;
            for (int &j : g) {
                check(bool(in >> j) && j >= 0 && j < 42 && !(seen >> j & 1), "Invalid permutation");
                seen |= Word{1} << j;
            }
            for (int r = 0; r < 21; ++r)
                for (int c = 0; c < 21; ++c) {
                    auto [a, b] = std::minmax(g[r], g[21 + c]);
                    check(a < 21 && b >= 21 &&
                              ((board.sites[r].zeros >> c) & 1) ==
                                  ((board.sites[a].zeros >> (b - 21)) & 1),
                          "Map changes a cell");
                }
            for (int k = 0; k < 6; ++k)
                for (unsigned t = 1; t < 128; ++t)
                    perm.chunks[k][t] =
                        perm.chunks[k][t & (t - 1)] | (Word{1} << g[7 * k + std::countr_zero(t)]);
        }
        in >> count;
        check(count == 2487, "Wrong number of marked pairs");
        for (int i = 0; i < count; ++i) {
            int a, b, size;
            in >> a >> b >> size;
            check(a >= 0 && a < n && b >= 0 && b < n && a != b && size > 0 &&
                      groupOrder % size == 0,
                  "Invalid pair root");
            check(members[a].rank <= members[b].rank, "Invalid pair shape order");
            Root root{a, b, {}};
            std::vector<bool> used(maps.size());
            for (int j = 0; j < size; ++j) {
                int k;
                check(bool(in >> k) && k >= 0 && k < int(maps.size()) && !used[k],
                      "Invalid stabilizer");
                for (int v : {a, b})
                    check(maps[k](members[v].box.key()) == members[v].box.key(),
                          "Map moves marked rectangle");
                root.maps.push_back(k);
                used[k] = true;
            }
            roots.push_back(std::move(root));
        }
    }

    int orbit(int k, const std::vector<int> &group, std::vector<bool> &seen) const {
        int count = 0;
        for (int g : group) {
            int v = index.at(maps[g](members[k].box.key()));
            check(v >= k && members[v].rank == members[k].rank,
                  "Third or fourth rectangle orbit differs");
            if (!seen[v]) {
                seen[v] = true;
                ++count;
            }
        }
        check(seen[k] && count > 0 && group.size() % count == 0, "Incomplete rectangle orbit");
        return count;
    }

    static bool small(const Ordinary &box) {
        return box.rank == 0 || box.rank == 7;
    }
    static void receipt(const FilterCounts &s, Word states) {
        std::cout << " " << s.local << " " << s.domination << " " << s.parity << " " << s.balance
                  << " " << s.feasible << " " << s.profiles << " " << states << std::endl;
    }

    bool run(int anchor, int m, const Board &board, const Profiles &profiles, bool smallOnly,
             std::ostream *core = nullptr) const {
        auto &root = roots[anchor];
        const auto &a = members[root.a];
        const auto &b = members[root.b];
        std::vector<bool> seen(members.size());
        Residual base;
        for (int i = 0; i < 42; ++i)
            base[i] = ~(a.box.cover[i] | b.box.cover[i]);
        Word mass = 0, cases = 0, orbits = 0, stamp = 14695981039346656037ull;
        FilterCounts stats;
        Completion search(board);
        for (int k = 0; k < int(members.size()); ++k) {
            const auto &c = members[k];
            if (k == root.a || k == root.b || c.rank < b.rank)
                continue;
            if (smallOnly && !small(a) && !small(b) && !small(c))
                continue;
            ++orbits;
            if (seen[k])
                continue;
            int size = orbit(k, root.maps, seen);
            int types = 1 + (a.rank != b.rank) + (b.rank != c.rank);
            mass += Word(types == 3 ? 6 : (types == 2 ? 3 : 1)) * (groupOrder / root.maps.size()) *
                    size;
            ++cases;
            stamp = (stamp ^ c.box.key()) * 1099511628211ull;
            Residual target;
            for (int i = 0; i < 42; ++i)
                target[i] = base[i] & ~c.box.cover[i];
            auto visit = [&](const Margins &d) { return search.profile(m, d, target); };
            Word before = stats.balance + stats.feasible, priorProfiles = stats.profiles;
            if (profiles.enumerate(m, target, stats, visit)) {
                std::cout << "COVER " << anchor << " " << root.a << " " << root.b << " " << k;
                search.solution.each([](int j) { std::cout << " " << j; });
                std::cout << std::endl;
                return true;
            }
            if (core && before != stats.balance + stats.feasible)
                *core << anchor << ' ' << k << ' ' << stats.profiles - priorProfiles << '\n';
        }
        check(cases ==
                  stats.local + stats.domination + stats.parity + stats.balance + stats.feasible,
              "Incomplete decisions");
        std::cout << "PAIR " << anchor << " " << cases << " " << mass << " " << orbits << " "
                  << stamp;
        receipt(stats, search.nodes);
        return false;
    }
    bool four(int anchor, int m, const Board &board, const Profiles &profiles,
              const std::string &mode) const {
        bool oneSmall = mode == "four-one", large = mode == "four-large";
        const Root &root = roots[anchor];
        const Ordinary &a = members[root.a];
        const Ordinary &b = members[root.b];
        if (int(small(a)) + int(small(b)) != (large ? 0 : (oneSmall ? 1 : 2)))
            return false;
        int otherRank = small(a) ? b.rank : a.rank;
        Word grandN = 0, grandMass = 0, grandEligible = 0, grandStamp = 14695981039346656037ull,
             grandStates = 0;
        FilterCounts grand;
        std::vector<bool> seenC(members.size());
        for (int k = 0; k < int(members.size()); ++k) {
            if (k == root.a || k == root.b || seenC[k])
                continue;
            const Ordinary &c = members[k];
            if ((oneSmall && (small(c) || c.rank < otherRank)) ||
                (large && (small(c) || c.rank < b.rank)))
                continue;
            int orbitC = orbit(k, root.maps, seenC);
            std::vector<int> fixed;
            for (int g : root.maps)
                if (maps[g](c.box.key()) == c.box.key())
                    fixed.push_back(g);
            check(fixed.size() * orbitC == root.maps.size(), "Third stabilizer mismatch");
            Residual base;
            for (int j = 0; j < 42; ++j)
                base[j] = ~(a.box.cover[j] | b.box.cover[j] | c.box.cover[j]);
            std::vector<bool> seenD(members.size());
            FilterCounts stats;
            Completion search(board);
            Word n = 0, mass = 0, eligible = 0, stamp = 14695981039346656037ull;
            for (int l = 0; l < int(members.size()); ++l) {
                const Ordinary &d = members[l];
                if (l == root.a || l == root.b || l == k || d.rank < c.rank ||
                    ((oneSmall || large) && small(d)))
                    continue;
                ++eligible;
                if (seenD[l])
                    continue;
                int size = orbit(l, fixed, seenD);
                int h = 2 + small(c) + small(d);
                int markings =
                    (h * (h - 1) / 2) * (1 + (a.rank == b.rank)) * (1 + (c.rank == d.rank));
                if (oneSmall) {
                    int kinds = 1 + (otherRank != c.rank) + (c.rank != d.rank);
                    markings = kinds == 3 ? 1 : (kinds == 2 ? 2 : 6);
                }
                if (large) {
                    int run = 1;
                    markings = 1;
                    std::array<int, 4> ranks{a.rank, b.rank, c.rank, d.rank};
                    for (int j = 1; j < 4; ++j) {
                        run = ranks[j] == ranks[j - 1] ? run + 1 : 1;
                        markings *= run;
                    }
                }
                check(24 % markings == 0, "Nonintegral symmetry weight");
                mass += Word(24 / markings) * (groupOrder / fixed.size()) * size;
                ++n;
                stamp = (stamp ^ d.box.key()) * 1099511628211ull;
                Residual target;
                for (int j = 0; j < 42; ++j)
                    target[j] = base[j] & ~d.box.cover[j];
                auto visit = [&](const Margins &deg) { return search.profile(m, deg, target); };
                if (profiles.enumerate(m, target, stats, visit)) {
                    std::cout << "COVER4 " << anchor << " " << root.a << " " << root.b << " " << k
                              << " " << l;
                    search.solution.each([](int j) { std::cout << " " << j; });
                    std::cout << std::endl;
                    return true;
                }
            }
            check(n == stats.local + stats.domination + stats.parity + stats.balance +
                           stats.feasible,
                  "Incomplete four-rectangle decisions");
            if (large) {
                grandN += n;
                grandMass += mass;
                grandEligible += eligible;
                grandStamp = (grandStamp ^ stamp) * 1099511628211ull;
                grand.local += stats.local;
                grand.domination += stats.domination;
                grand.parity += stats.parity;
                grand.balance += stats.balance;
                grand.feasible += stats.feasible;
                grand.profiles += stats.profiles;
                grandStates += search.nodes;
            } else {
                std::cout << "QUAD " << anchor << " " << k << " " << n << " " << mass << " "
                          << eligible << " " << stamp;
                receipt(stats, search.nodes);
            }
        }
        if (large) {
            std::cout << "LARGE " << anchor << " " << grandN << " " << grandMass << " "
                      << grandEligible << " " << grandStamp;
            receipt(grand, grandStates);
        }
        return false;
    }
};

int main(int argc, char **argv) {
    try {
        check(argc >= 6 && argc <= 8,
              "Usage: scan inventory hexads first end stride [mode [residual-file]]");
        std::ifstream input(argv[1]);
        check(bool(input), "Cannot open geometry input");
        static Board board;
        board.read(input);
        Inventory inventory;
        inventory.read(board, input);
        Profiles profiles(board);
        int m = std::stoi(argv[2]), first = std::stoi(argv[3]), end = std::stoi(argv[4]),
            step = std::stoi(argv[5]);
        check(m >= 1 && m <= 15 && first >= 0 && end <= int(inventory.roots.size()) && step > 0,
              "Invalid range");
        std::string mode = argc >= 7 ? argv[6] : "all";
        std::ofstream core;
        if (argc == 8) {
            core.open(argv[7]);
            check(bool(core), "Cannot open residual file");
        }
        check(mode == "all" || mode == "small" || mode == "four" || mode == "four-one" ||
                  mode == "four-large",
              "Unknown inventory");
        for (int i = first; i < end; i += step) {
            bool found = mode.starts_with("four")
                             ? inventory.four(i, m, board, profiles, mode)
                             : inventory.run(i, m, board, profiles, mode == "small",
                                             argc == 8 ? &core : nullptr);
            if (found)
                break;
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
