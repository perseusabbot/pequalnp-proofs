// Independent checker using freely available signatures and the binary leaf bound.
// Compile with a C++17 compiler. Arguments are the missing-edge mask, sample vertex mask, and gate cap.
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
    Word target = 0, allRows = 0;
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

    // Look only at complete sets of available signals. A minimum program using
    // k more gates has at most k+1 distinct terminals in its output cone.
    // If a gate is cut, its result must occur in the continuation of a minimum
    // program. Any other available signals may be omitted, including signals
    // unrelated to either operand of the gate.
    bool possible(const State& available, int cap) {
        if (std::binary_search(available.begin(),available.end(),target)) return true;
        if (!cap || available.size()<2) return false;
        if (!visited[cap].insert(available).second) return false;

        const int n=static_cast<int>(available.size());
        std::vector<Pairs> cov(n), exclusive(n);
        Pairs seen,twice;
        for (int i=0;i<n;++i) {
            cov[i]=coverage(available[i]);
            twice |= seen & cov[i];
            seen |= cov[i];
        }
        if (seen!=required) return false;
        for (int i=0;i<n;++i) exclusive[i]=cov[i] & ~twice;

        if (n>cap+1) {
            // Enumerate root supports directly. A superset of the actual cone
            // is sufficient. Distinctions unique to an input force inclusion.
            State chosen,optional;
            Pairs prefix;
            for (int i=0;i<n;++i) {
                if (exclusive[i].any()) {chosen.push_back(available[i]);prefix|=cov[i];}
                else optional.push_back(available[i]);
            }
            if (static_cast<int>(chosen.size())>cap+1) return false;
            return choose(optional,0,chosen,prefix,cap);
        }

        std::unordered_set<Word> generated;
        const int omit=std::max(0,n+1-cap);
        for (int a=0;a<n;++a) for (int b=a+1;b<n;++b) {
            for (Word fresh : {available[a]&available[b],available[a]|available[b]}) {
                if (fresh==target) return true;
                if (fresh==0 || fresh==allRows || std::binary_search(available.begin(),available.end(),fresh)
                    || !generated.insert(fresh).second) continue;
                const Pairs fc=coverage(fresh);
                std::vector<int> optional;
                if (omit) {
                    for (int i=0;i<n;++i)
                        if ((exclusive[i] & ~fc).none()) optional.push_back(i);
                    if (static_cast<int>(optional.size())<omit) continue;
                }
                auto child=[&](int drop1,int drop2) {
                    if (drop2>=0) {
                        // Check that jointly omitting two inputs still separates
                        // every positive / negative pair.
                        Pairs cover=fc;
                        for (int i=0;i<n;++i) if (i!=drop1 && i!=drop2) cover|=cov[i];
                        if (cover!=required) return false;
                    }
                    State next;
                    next.reserve(n+1-omit);
                    for (int i=0;i<n;++i) if (i!=drop1 && i!=drop2) next.push_back(available[i]);
                    next.insert(std::lower_bound(next.begin(),next.end(),fresh),fresh);
                    return possible(next,cap-1);
                };
                if (omit==0 && child(-1,-1)) return true;
                if (omit==1) {
                    for (int i : optional) if (child(i,-1)) return true;
                }
                if (omit==2) {
                    for (unsigned i=0;i<optional.size();++i)
                        for (unsigned j=0;j<i;++j) if (child(optional[i],optional[j])) return true;
                }
            }
        }
        return false;
    }

    bool choose(const State& optional,int at,State& chosen,Pairs seen,int cap) {
        int need=cap+1-static_cast<int>(chosen.size());
        if (!need) {
            if (seen!=required) return false;
            State root=chosen;
            std::sort(root.begin(),root.end());
            return possible(root,cap);
        }
        for (int i=at;i+need<=static_cast<int>(optional.size());++i) {
            chosen.push_back(optional[i]);
            if (choose(optional,i+1,chosen,seen|coverage(optional[i]),cap)) return true;
            chosen.pop_back();
        }
        return false;
    }

public:
    Search(int lost, int vertices, int cap) : visited(cap+1) {
        std::array<int,14> survivors{};
        for (int i = 0; i < 21; ++i) {
            auto [a,b] = edges[i];
            if (lost & bit(i)) {
                int e=bit(a)|bit(b);
                if ((vertices&e)==e) positive.push_back(e);
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
        if (positive.empty() || negative.empty() || positive.size()+negative.size() > 64 || positive.size()*negative.size()>required.size())
            throw std::invalid_argument("The row set exceeds the word width");
        for (std::size_t i = 0; i < positive.size()*negative.size(); ++i) required.set(i);
        allRows=~Word(0) >> (64-positive.size()-negative.size());
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
    if (argc != 4) { std::cerr << "Usage: availability MISSING_MASK VERTEX_MASK GATE_CAP\n"; return 2; }
    int mask = std::stoi(argv[1]), vertices = std::stoi(argv[2]), cap = std::stoi(argv[3]);
    if (mask <= 0 || mask >= bit(21) || vertices<=0 || vertices>=bit(14) || cap < 0 || cap > 26) return 2;
    Search(mask,vertices,cap).report(mask,cap);
}
