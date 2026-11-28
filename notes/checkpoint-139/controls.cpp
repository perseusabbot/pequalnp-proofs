#include "complete.hpp"
#include "profiles.hpp"
#include <fstream>

int main(int argc, char **argv) {
    try {
        check(argc == 2, "Usage: controls board");
        std::ifstream file(argv[1]);
        static Board b;
        b.read(file);
        Profiles profiles(b);
        int size;
        while (std::cin >> size) {
            check(1 <= size && size <= 16, "Invalid control size");
            Family known{};
            Margins requested{};
            Residual target{};
            for (int t = 0; t < size; ++t) {
                int j;
                check(bool(std::cin >> j) && j >= 0 && j < 168 && !known.has(j),
                      "Control ID differs");
                known.set(j);
                for (int i : b.membership[j]) {
                    ++requested[i];
                    target[i] |= b.maximum[j].cover[i];
                }
            }
            auto verify = [&](const Family &choice, const Margins &d) {
                Margins actual{};
                Residual covered{};
                choice.each([&](int j) {
                    for (int i : b.membership[j]) {
                        ++actual[i];
                        covered[i] |= b.maximum[j].cover[i];
                    }
                });
                check(actual == d && choice.count() == size, "Wrong witness degree sequence");
                for (int i = 0; i < 42; ++i)
                    check(!(target[i] & ~covered[i]), "Incomplete control coverage");
            };
            Completion search(b);
            check(search.profile(size, requested, target), "Known profile rejected");
            verify(search.solution, requested);
            std::cout << "EXACT " << size << " " << search.nodes;
            search.solution.each([](int j) { std::cout << " " << j; });
            std::cout << std::endl;
            if (size <= 10) {
                Completion free(b);
                FilterCounts stats;
                auto visit = [&](const Margins &d) {
                    if (!free.profile(size, d, target))
                        return false;
                    verify(free.solution, d);
                    return true;
                };
                check(profiles.enumerate(size, target, stats, visit), "Known cover rejected");
                std::cout << "SEARCH " << size << " " << stats.profiles << " " << free.nodes;
                free.solution.each([](int j) { std::cout << " " << j; });
                std::cout << std::endl;
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
