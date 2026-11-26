// Independent search for four moving orbits and three fixed rectangles.
// Choose the moving orbits first, on the cells that no fixed rectangle can hit.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

using Word = std::uint64_t;

struct Board {
    Word low, high;
    bool empty() const { return !(low | high); }
    Board without(Board other) const { return {low & ~other.low, high & ~other.high}; }
    bool has(int i) const { return i < 64 ? (low >> i) & 1 : (high >> (i-64)) & 1; }
};

struct Orbit { Board cells; Word boundary; };

struct Search {
    int sites, rim;
    Board full;
    std::vector<Board> fixed;
    std::vector<Orbit> moving;
    std::vector<int> anchors, all;
    std::array<std::vector<int>,128> fixedAt;
    std::vector<std::vector<int>> triples;
    std::uint64_t completions = 0;

    int key(int a, int b, int c) const { return (a*rim+b)*rim+c; }

    bool fixedFinish(Board need, int slots) const {
        if (need.empty()) return true;
        if (slots == 0) return false;
        int pivot = -1;
        for (int i = 0; i < sites; ++i)
            if (need.has(i) && (pivot < 0 || fixedAt[i].size() < fixedAt[pivot].size())) pivot = i;
        for (int j : fixedAt[pivot])
            if (fixedFinish(need.without(fixed[j]), slots-1)) return true;
        return false;
    }

    const std::vector<int>& possibleLast(Word missing) const {
        const std::vector<int>* best = &all;
        // Every final orbit must be in each such posting. Testing any one of
        // them and then testing the complete missing word is sufficient.
        while (std::popcount(missing) >= 3) {
            int a = std::countr_zero(missing); missing &= missing-1;
            int b = std::countr_zero(missing); missing &= missing-1;
            int c = std::countr_zero(missing); missing &= missing-1;
            const auto& list = triples[key(a,b,c)];
            if (list.size() < best->size()) best = &list;
        }
        return *best;
    }

    bool complete(int index) {
        const Orbit a = moving[index];
        Word left = ((Word(1) << rim)-1) & ~a.boundary;
        std::vector<std::pair<int,int>> order;
        for (int i : all) {
            if (i != index && std::popcount(moving[i].boundary) <= std::popcount(a.boundary))
                order.emplace_back(std::popcount(left & moving[i].boundary), i);
        }
        std::sort(order.rbegin(), order.rend());
        for (int i = 0; i < static_cast<int>(order.size()); ++i) {
            auto [gain, b] = order[i];
            if (3*gain < std::popcount(left)) break;
            Word rest = left & ~moving[b].boundary;
            for (int j = i+1; j < static_cast<int>(order.size()); ++j) {
                auto [cap, c] = order[j];
                if (2*cap < std::popcount(rest)) break;
                Word missing = rest & ~moving[c].boundary;
                if (2*std::popcount(missing) > std::popcount(rest)) continue;
                for (int d : possibleLast(missing)) {
                    if (missing & ~moving[d].boundary) continue;
                    ++completions;
                    Board need = full.without(a.cells).without(moving[b].cells)
                                     .without(moving[c].cells).without(moving[d].cells);
                    if (fixedFinish(need, 3)) return true;
                }
            }
        }
        return false;
    }

    bool read() {
        int nf, nm, na;
        if (!(std::cin >> sites >> rim >> nf >> nm >> na) || sites < 65 || sites > 127 ||
            rim < 1 || rim > 63 || nf < 3 || nm < 4 || na < 1) return false;
        full = {~Word(0), (Word(1) << (sites-64))-1};
        fixed.resize(nf); moving.resize(nm); anchors.resize(na); triples.resize(rim*rim*rim);
        for (int i = 0; i < nf; ++i) {
            auto& w = fixed[i];
            if (!(std::cin >> w.low >> w.high)) return false;
            for (int j = 0; j < sites; ++j) if (w.has(j)) fixedAt[j].push_back(i);
        }
        for (int i = 0; i < nm; ++i) {
            auto& m = moving[i];
            if (!(std::cin >> m.cells.low >> m.cells.high >> m.boundary) || m.boundary >> rim) return false;
            std::vector<int> digits;
            for (Word w = m.boundary; w; w &= w-1) digits.push_back(std::countr_zero(w));
            int n = static_cast<int>(digits.size());
            for (int a = 0; a < n; ++a)
                for (int b = a+1; b < n; ++b)
                    for (int c = b+1; c < n; ++c)
                        triples[key(digits[a],digits[b],digits[c])].push_back(i);
            all.push_back(i);
        }
        for (auto& i : anchors) if (!(std::cin >> i) || i < 0 || i >= nm) return false;
        return true;
    }
};

int main() {
    Search search;
    if (!search.read()) return 1;
    for (int i : search.anchors) {
        if (search.complete(i)) {
            std::cerr << "Feasible moving anchor " << i << '\n';
            return 2;
        }
    }
    std::cout << search.anchors.size() << ' ' << search.completions << '\n';
}
