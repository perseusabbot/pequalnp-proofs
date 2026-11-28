#include "complete.hpp"
#include "profiles.hpp"
#include <fstream>
#include <map>
#include <string>

int main(int argc, char **argv) {
    try {
        check(argc == 5, "Usage: patterns board low-sets selected limit");
        std::ifstream geometry(argv[1]), sets(argv[2]);
        check(geometry.good() && sets.good(), "Missing input");
        static Board board;
        board.read(geometry);
        Profiles profiles(board);
        int m = std::stoi(argv[3]), limit = std::stoi(argv[4]);
        Mask rows, cols;
        Word multiplicity;
        while (sets >> rows >> cols >> multiplicity) {
            int size = std::popcount(rows) + std::popcount(cols);
            if (size > limit)
                continue;
            Margins low{};
            for (int i = 0; i < 42; ++i)
                low[i] = ((i < 21 ? rows : cols) >> (i % 21) & 1) ? 0 : 3;
            FilterCounts stats;
            Completion search(board);
            Word capped = 0, compatible = 0;
            std::map<int, Word> coverage;
            Family witness{};
            search.onSolution = [&](const Family &selected) {
                std::array<Mask, 21> unionRows{};
                selected.each([&](int id) {
                    const auto &h = board.maximum[id];
                    for (Mask r = h.axes[0]; r; r &= r - 1)
                        unionRows[std::countr_zero(r)] |= h.axes[1];
                });
                int cells = 0;
                for (Mask row : unionRows)
                    cells += std::popcount(row);
                if (coverage.empty() || cells > coverage.rbegin()->first)
                    witness = selected;
                ++coverage[cells];
                return false; // Enumerate every family for this exact degree assignment.
            };
            auto visit = [&](const Margins &d) {
                for (int i = 0; i < 42; ++i)
                    if (!low[i] && d[i] > 2)
                        return false;
                ++capped;
                for (int i = 0; i < 21; ++i)
                    for (int j : board.sites[i].incident)
                        if (d[i] + d[j] > m)
                            return false;
                ++compatible;
                return search.profile(m, d, Residual{});
            };
            profiles.bounds(m, low, stats, visit);
            bool yes = !coverage.empty();
            std::cout << (yes ? "WITNESS" : "EXCLUDED") << " " << rows << " " << cols << " "
                      << multiplicity << " " << stats.profiles << " " << capped << " " << compatible
                      << " " << search.nodes;
            std::cout << " " << coverage.size();
            for (auto [cells, n] : coverage)
                std::cout << " " << cells << " " << n;
            if (yes)
                witness.each([](int j) { std::cout << " " << j; });
            std::cout << std::endl;
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
