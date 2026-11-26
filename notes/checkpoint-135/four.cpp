// Complete a supplied residual with at most four moving orbits on a 65–127 cell quotient.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Word = std::uint64_t;

struct Mask {
    Word low, high;
    int size() const { return std::popcount(low) + std::popcount(high); }
    bool empty() const { return low == 0 && high == 0; }
    Mask operator&(Mask other) const { return {low & other.low, high & other.high}; }
    Mask operator|(Mask other) const { return {low | other.low, high | other.high}; }
    Mask without(Mask other) const { return {low & ~other.low, high & ~other.high}; }
    bool operator==(const Mask&) const = default;
    bool operator<(Mask other) const {
        return high == other.high ? low < other.low : high < other.high;
    }
};

template<class Function>
void eachCell(Mask mask, Function f) {
    for (Word w = mask.low; w; w &= w-1) f(std::countr_zero(w));
    for (Word w = mask.high; w; w &= w-1) f(64 + std::countr_zero(w));
}

bool fourSuffice(Mask need, const std::vector<Mask>& moving, std::uint64_t& queries) {
    if (need.empty()) return true;
    std::vector<Mask> words;
    words.reserve(moving.size());
    int largest = 0;
    for (Mask m : moving) {
        Mask w = m & need;
        words.push_back(w);
        largest = std::max(largest, w.size());
    }
    if (4*largest < need.size()) return false;
    std::sort(words.begin(), words.end());
    words.erase(std::unique(words.begin(), words.end()), words.end());
    // Bucketing preserves the ascending word order on ties without repeatedly
    // counting bits inside a sorting comparator.
    std::array<std::vector<Mask>,129> byArea;
    for (Mask w : words) byArea[w.size()].push_back(w);
    words.clear();
    for (int area = largest; area >= 0; --area)
        words.insert(words.end(), byArea[area].begin(), byArea[area].end());

    std::array<std::vector<int>,128> contains;
    bool indexed = false;
    auto canFinish = [&](Mask missing) {
        ++queries;
        if (missing.empty()) return true;
        if (!indexed) {
            for (int i = 0; i < static_cast<int>(words.size()); ++i)
                eachCell(words[i], [&](int c) { contains[c].push_back(i); });
            indexed = true;
        }
        int rarest = -1;
        eachCell(missing, [&](int c) {
            if (rarest < 0 || contains[c].size() < contains[rarest].size()) rarest = c;
        });
        for (int d : contains[rarest])
            if (missing.without(words[d]).empty()) return true;
        return false;
    };

    // Order the first member by total area and the second by marginal area.
    // Among the final two members at least one must hit half of what remains.
    const int required = need.size();
    for (int first = 0; first < static_cast<int>(words.size()); ++first) {
        int area = words[first].size();
        if (4*area < required) break;
        Mask left = need.without(words[first]);
        if (left.empty()) return true;
        int missing = left.size();
        std::array<std::vector<int>,129> buckets;
        for (int i = first+1; i < static_cast<int>(words.size()); ++i) {
            int gain = (words[i] & left).size();
            if (gain >= missing - 2*area) buckets[gain].push_back(i);
        }
        std::vector<int> choices;
        for (int gain = area; gain >= 0; --gain)
            choices.insert(choices.end(), buckets[gain].begin(), buckets[gain].end());
        for (int second = 0; second < static_cast<int>(choices.size()); ++second) {
            Mask b = words[choices[second]];
            if (3*(b & left).size() < missing) break;
            Mask rest = left.without(b);
            if (rest.empty()) return true;
            int half = (rest.size()+1)/2;
            for (int third = second+1; third < static_cast<int>(choices.size()); ++third) {
                Mask c = words[choices[third]];
                if ((c & left).size() < half) break;
                if ((c & rest).size() >= half && canFinish(rest.without(c))) return true;
            }
        }
    }
    return false;
}

int main() {
    int cells, count, cases;
    if (!(std::cin >> cells >> count >> cases) || cells < 65 || cells > 127 ||
        count < 1 || cases < 1) return 1;
    const Mask board{~Word(0), (Word(1) << (cells-64))-1};
    std::vector<Mask> moving(count);
    for (auto& w : moving)
        if (!(std::cin >> w.low >> w.high) || !w.without(board).empty()) return 1;
    std::uint64_t total = 0;
    for (int k = 0; k < cases; ++k) {
        Mask covered;
        if (!(std::cin >> covered.low >> covered.high) || !covered.without(board).empty()) return 1;
        if (fourSuffice(board.without(covered), moving, total)) {
            std::cerr << "Four moving orbits cover residual " << k << '\n';
            return 2;
        }
    }
    std::cout << cases << ' ' << total << '\n';
}
