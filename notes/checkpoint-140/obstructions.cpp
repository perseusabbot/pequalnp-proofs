// Test whether a residual after nine maximum rectangles can avoid a five-cell fooling set.
#include "coloring.hpp"

int main(int argc, char **argv) {
    try {
        require(argc == 6, "Usage: obstructions board six-subsets start stop stride");
        Geometry b(argv[1]);
        Conflicts g(b);
        Scores scores(b);
        auto seeds = readSeeds(argv[2]);
        int start = std::stoi(argv[3]), stop = std::stoi(argv[4]), stride = std::stoi(argv[5]);
        require(start >= 0 && stop >= start && stride > 0, "Invalid search range");
        for (int z = start; z < std::min(stop, int(seeds.size())); z += stride) {
            const auto &s = seeds[z].h;
            auto base = scores.base(s);
            Cells holes = Cells::full();
            HSet all = HSet::full();
            for (int j : s) {
                holes.remove(g.boxes[j]);
                all.erase(j);
            }
            HSet eligible = all;
            g.seven.unhit(s, [&](const HSet &miss) { eligible.remove(miss); });
            std::array<HSet, 168> edge;
            edge.fill(all);
            g.six.unhit(s,
                        [&](const HSet &miss) { miss.each([&](int x) { edge[x].remove(miss); }); });
            HSet later = all;
            Word pairs = 0, triangles = 0, marked = 0, stamp = 14695981039346656037ULL;
            all.each([&](int i) {
                later.erase(i);
                const auto neighbors = later & edge[i];
                pairs += neighbors.count();
                if (!eligible.has(i))
                    return;
                neighbors.each([&](int j) {
                    if (!eligible.has(j))
                        return;
                    (neighbors & edge[j] & eligible).each([&](int k) {
                        if (k <= j)
                            return;
                        ++triangles;
                        if (!scores.canonical<3>(s, base, {i, j, k}))
                            return;
                        ++marked;
                        Cells h = holes;
                        h.remove(g.boxes[i]);
                        h.remove(g.boxes[j]);
                        h.remove(g.boxes[k]);
                        std::array<int, 5> selected;
                        Coloring<5> collector(g);
                        require(collector.find(h, 5, selected),
                                "Nine rectangles leave no five-cell witness");
                        auto distinct = selected;
                        std::sort(distinct.begin(), distinct.end());
                        require(std::adjacent_find(distinct.begin(), distinct.end()) ==
                                    distinct.end(),
                                "Repeated witness cell");
                        for (auto v : selected) {
                            require(h.has(v), "Witness is covered");
                            for (auto u : selected)
                                if (u != v) {
                                    auto [p, l] = g.cell[v];
                                    auto [q, m] = g.cell[u];
                                    require(!((b.rows[p] >> m) & (b.rows[q] >> l) & 1),
                                            "Two witness cells fit in one rectangle");
                                }
                            stamp = (stamp ^ Word(v + 1)) * 1099511628211ULL;
                        }
                    });
                });
            });
            std::cout << z << " " << seeds[z].weight << " " << pairs << " " << triangles << " "
                      << marked << " " << stamp << '\n';
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
