// Reconstruct the positive degree-profile cases without quotienting the fourth rectangle.
#include "profiles.hpp"
#include <fstream>

int main(int argc, char **argv) {
    try {
        check(argc == 3, "Usage: four_filter inventory prefixes");
        std::ifstream in(argv[1]), roots(argv[2]);
        static Board board;
        board.read(in);
        Profiles pr(board);
        int n;
        in >> n;
        check(n == 25067, "Wrong number of rectangles");
        std::vector<Box> boxes;
        std::vector<int> rank;
        for (int i = 0; i < n; ++i) {
            Mask a, b;
            int r;
            in >> a >> b >> r;
            boxes.push_back(board.box(a, b));
            rank.push_back(r);
        }
        int small, anchor, a, b, c;
        while (roots >> small >> anchor >> a >> b >> c) {
            Residual base;
            for (int i = 0; i < 42; ++i)
                base[i] = ~(boxes[a].cover[i] | boxes[b].cover[i] | boxes[c].cover[i]);
            for (int d = 0; d < n; ++d) {
                if (d == a || d == b || d == c || rank[d] < rank[c])
                    continue;
                if (small == 1 && (rank[d] == 0 || rank[d] == 7))
                    continue;
                Residual target;
                for (int j = 0; j < 42; ++j)
                    target[j] = base[j] & ~boxes[d].cover[j];
                FilterCounts stats;
                auto visit = [](const Margins &) { return false; };
                pr.enumerate(9, target, stats, visit);
                if (stats.profiles)
                    std::cout << small << " " << anchor << " " << c << " " << d << " "
                              << stats.profiles << '\n';
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
