// Independent checker using freely available signatures and the binary leaf bound.
// Compile with a C++17 compiler. Arguments are the missing-edge mask and gate cap.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
using State = std::vector<Word>;
using Pairs = std::bitset<512>;

constexpr std::array<std::pair<int, int>, 21> edges{{
    {0,7},{0,8},{0,10},{1,7},{1,9},{1,13},{2,8},{2,12},{2,13},{3,7},{3,11},
    {3,12},{4,10},{4,11},{4,13},{5,9},{5,10},{5,12},{6,8},{6,9},{6,11}
}};

int bit(int v) { return 1 << v; }

struct Hash {
    std::size_t operator()(const State& state) const {
        std::size_t value = 1;
        for (Word signal : state) value = (value ^ signal) * 1099511628211ULL;
        return value;
    }
};

class Search {
    std::vector<std::unordered_set<State, Hash>> visited;
    std::unordered_map<Word, Pairs> distinguishes;
    std::vector<int> positive, negative;
    Pairs required;
    Word target = 0;
    State initial;

    Pairs coverage(Word signal) {
        auto found = distinguishes.find(signal);
        if (found != distinguishes.end()) return found->second;
        Pairs result;
        for (std::size_t i = 0; i < positive.size(); ++i) {
            if (!(signal & (Word(1) << i))) continue;
            for (std::size_t j = 0; j < negative.size(); ++j) {
                if (!(signal & (Word(1) << (positive.size()+j)))) {
                    result.set(i*negative.size()+j);
                }
            }
        }
        distinguishes.emplace(signal,result);
        return result;
    }

    bool possible(const State& available, int cap) {
        if (std::binary_search(available.begin(),available.end(),target)) return true;
        if (cap == 0) return false;
        Pairs seen, twice;
        std::vector<Pairs> cover;
        for (Word signal : available) {
            cover.push_back(coverage(signal));
            twice |= seen & cover.back();
            seen |= cover.back();
        }
        if (seen != required) return false;

        // A pair separated by only one signal forces that terminal to occur.
        std::vector<std::size_t> optional;
        for (std::size_t i = 0; i < cover.size(); ++i) {
            if ((cover[i] & ~twice).none()) optional.push_back(i);
        }
        if (available.size() - optional.size() > static_cast<std::size_t>(cap+1)) return false;
        if (!visited[cap].insert(available).second) return false;
        if (available.size() > static_cast<std::size_t>(cap+1)) {
            // A cone with at most cap binary gates can read at most cap+1 terminals.
            for (auto i : optional) {
                State smaller = available;
                smaller.erase(smaller.begin()+i);
                if (possible(smaller,cap)) return true;
            }
            return false;
        }
        // Cut a gate whose two operands are terminals. All old signals remain
        // freely available. A minimum circuit gains nothing by recreating one.
        for (std::size_t i = 0; i < available.size(); ++i) {
            for (std::size_t j = i+1; j < available.size(); ++j) {
                Word a = available[i], b = available[j];
                for (Word fresh : {a & b,a | b}) {
                    auto place = std::lower_bound(available.begin(),available.end(),fresh);
                    if (place != available.end() && *place == fresh) continue;
                    State next = available;
                    next.insert(next.begin() + (place-available.begin()),fresh);
                    if (possible(next,cap-1)) return true;
                }
            }
        }
        return false;
    }

public:
    Search(int lost, int cap) : visited(cap+1) {
        int vertices = 0;
        std::array<int,14> survivors{};
        for (int i = 0; i < 21; ++i) {
            auto [a,b] = edges[i];
            if (lost & bit(i)) {
                positive.push_back(bit(a) | bit(b));
                vertices |= positive.back();
            } else {
                survivors[a] |= bit(b);
                survivors[b] |= bit(a);
            }
        }
        std::vector<int> internal;
        for (auto [a,b] : edges) {
            int edge = bit(a) | bit(b);
            if ((edge & vertices) == edge) internal.push_back(edge);
        }
        auto independent = [&](int row) {
            return std::none_of(internal.begin(),internal.end(),[row](int e) {return (row&e)==e;});
        };
        for (int row = 0; row < bit(14); ++row) {
            if ((row & vertices) != row || !independent(row)) continue;
            bool maximal = true;
            for (int v = 0; v < 14; ++v) {
                if ((vertices & ~row & bit(v)) && independent(row | bit(v))) maximal = false;
            }
            if (maximal) negative.push_back(row);
        }
        if (positive.size()+negative.size() >= 64 || positive.size()*negative.size()>required.size())
            throw std::invalid_argument("The row set exceeds the word width");
        for (std::size_t i = 0; i < positive.size()*negative.size(); ++i) required.set(i);
        target = (Word(1) << positive.size())-1;
        std::vector<int> rows = positive;
        rows.insert(rows.end(),negative.begin(),negative.end());
        std::set<int> masks;
        for (int v = 0; v < 14; ++v) {
            if (vertices & bit(v)) masks.insert(bit(v));
            int group = survivors[v] & vertices;
            for (int m = group; m; m = (m-1)&group) masks.insert(m);
        }
        for (int mask : masks) {
            Word signal = 0;
            for (std::size_t j = 0; j < rows.size(); ++j) {
                if (rows[j]&mask) signal |= Word(1) << j;
            }
            initial.push_back(signal);
        }
        std::sort(initial.begin(),initial.end());
        initial.erase(std::unique(initial.begin(),initial.end()),initial.end());
    }

    void report(int mask, int cap) {
        bool yes = possible(initial,cap);
        std::size_t states = 0;
        for (const auto& layer : visited) states += layer.size();
        std::cout << "{\"mask\":" << mask << ",\"cap\":" << cap << ",\"positive_rows\":" << positive.size()
                  << ",\"negative_rows\":" << negative.size() << ",\"input_signatures\":" << initial.size()
                  << ",\"possible\":" << (yes ? "true" : "false") << ",\"expanded_states\":" << states << "}\n";
    }
};

int main(int argc, char** argv) {
    if (argc != 3) { std::cerr << "Usage: availability MISSING_MASK GATE_CAP\n"; return 2; }
    int mask = std::stoi(argv[1]), cap = std::stoi(argv[2]);
    if (mask <= 0 || mask >= bit(21) || cap < 0 || cap > 26) return 2;
    Search(mask,cap).report(mask,cap);
}
