#include "coloring.hpp"
template <int K> void run(const Geometry &b, const Conflicts &g, Cells target) {
    Coloring<K> s(g);
    bool yes = s.cover(target);
    std::cout << (yes ? "COVER" : "EXCLUDED") << " " << s.nodes;
    if (yes) {
        std::array<unsigned, 21> rows{};
        for (auto group : s.answer) {
            unsigned a = 0, c = 0;
            group.each([&](int j) {
                auto [r, q] = g.cell[j];
                a |= 1u << r;
                c |= 1u << q;
            });
            for (unsigned t = a; t; t &= t - 1) {
                int p = std::countr_zero(t);
                require(!(c & ~b.rows[p]), "Illegal positive rectangle");
                rows[p] |= c;
            }
            std::cout << " " << a << " " << c;
        }
        target.each([&](int j) {
            auto [r, c] = g.cell[j];
            require(rows[r] >> c & 1, "Positive control leaves a hole");
        });
    }
    std::cout << '\n';
}
int main(int argc, char **argv) {
    try {
        require(argc == 2, "Usage: controls board");
        Geometry b(argv[1]);
        Conflicts g(b);
        int k;
        while (std::cin >> k) {
            Cells target;
            std::array<unsigned, 21> required{};
            for (auto &r : required)
                require(bool(std::cin >> r), "Missing target");
            for (int i = 0; i < 21; ++i)
                require(!(required[i] & ~b.rows[i]), "Illegal control target");
            for (int j = 0; j < 336; ++j) {
                auto [r, c] = g.cell[j];
                if (required[r] >> c & 1)
                    target.set(j);
            }
            switch (k) {
            case 4:
                run<4>(b, g, target);
                break;
            case 5:
                run<5>(b, g, target);
                break;
            case 6:
                run<6>(b, g, target);
                break;
            case 7:
                run<7>(b, g, target);
                break;
            case 8:
                run<8>(b, g, target);
                break;
            case 9:
                run<9>(b, g, target);
                break;
            default:
                throw std::runtime_error("Unsupported control budget");
            }
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
