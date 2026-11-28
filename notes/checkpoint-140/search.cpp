// Test whether a fixed family of maximum rectangles can be completed by unrestricted rectangles.
#include "coloring.hpp"
#include <sstream>

struct Record {
    std::vector<int> ids;
    Word mass;
};
inline std::vector<Record> records(const char *path, int fixed) {
    std::ifstream file(path);
    require(file.good(), "Missing anchors");
    std::vector<Record> out;
    Word mass = 0;
    std::string line;
    while (std::getline(file, line)) {
        std::istringstream in(line);
        Record r;
        r.ids.resize(fixed);
        for (int &i : r.ids)
            require(bool(in >> i) && i >= 0 && i < 168, "Invalid rectangle index");
        require(std::is_sorted(r.ids.begin(), r.ids.end()) &&
                    std::adjacent_find(r.ids.begin(), r.ids.end()) == r.ids.end(),
                "Repeated rectangle");
        require(bool(in >> r.mass) && r.mass > 0 && 241920 % r.mass == 0, "Invalid multiplicity");
        std::string tail;
        require(!(in >> tail), "Extra fields in orbit");
        mass += r.mass;
        out.push_back(std::move(r));
    }
    Word total = 1;
    for (int j = 1; j <= fixed; ++j)
        total = total * (169 - j) / j;
    require(mass == total, "Incomplete orbit list");
    return out;
}
template <int K> void test(const Geometry &b, const Conflicts &g, const Record &r, int id) {
    Cells holes = Cells::full();
    for (int j : r.ids)
        holes.remove(g.boxes[j]);
    Coloring<K> search(g);
    bool found = search.cover(holes);
    if (!found) {
        std::cout << "EXCLUDED " << id << " " << r.mass << " " << holes.count() << " "
                  << search.nodes << '\n';
        return;
    }
    std::vector<Axes> boxes;
    for (int j : r.ids)
        boxes.push_back(b.maximum[j]);
    for (const auto &w : search.answer)
        if (w.any()) {
            Axes a{};
            w.each([&](int j) {
                auto [p, q] = g.cell[j];
                a[0] |= 1u << p;
                a[1] |= 1u << q;
            });
            boxes.push_back(a);
        }
    std::array<unsigned, 21> covered{};
    for (auto [a, c] : boxes)
        for (unsigned u = a; u; u &= u - 1) {
            int p = std::countr_zero(u);
            require(!(c & ~b.rows[p]), "A color rectangle contains a one");
            covered[p] |= c;
        }
    require(covered == b.rows, "Incomplete candidate");
    std::cout << "COVER " << id << " " << r.mass << " " << holes.count() << " " << search.nodes
              << " " << boxes.size();
    for (auto [a, c] : boxes)
        std::cout << " " << a << " " << c;
    std::cout << std::endl;
}
int main(int argc, char **argv) {
    try {
        require(argc == 8, "Usage: search board seeds fixed colors start stop stride");
        int fixed = std::stoi(argv[3]), colors = std::stoi(argv[4]), start = std::stoi(argv[5]),
            stop = std::stoi(argv[6]), stride = std::stoi(argv[7]);
        require(fixed >= 1 && fixed <= 6 && colors >= 5 && colors <= 12 && start >= 0 &&
                    stop >= start && stride > 0,
                "Invalid search range");
        Geometry b(argv[1]);
        Conflicts g(b);
        auto seeds = records(argv[2], fixed);
        for (int i = start; i < std::min(stop, int(seeds.size())); i += stride) {
            switch (colors) {
            case 5:
                test<5>(b, g, seeds[i], i);
                break;
            case 6:
                test<6>(b, g, seeds[i], i);
                break;
            case 7:
                test<7>(b, g, seeds[i], i);
                break;
            case 8:
                test<8>(b, g, seeds[i], i);
                break;
            case 9:
                test<9>(b, g, seeds[i], i);
                break;
            case 10:
                test<10>(b, g, seeds[i], i);
                break;
            case 11:
                test<11>(b, g, seeds[i], i);
                break;
            case 12:
                test<12>(b, g, seeds[i], i);
                break;
            }
            if ((i - start) / stride % 32 == 0)
                std::cout.flush();
        }
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
