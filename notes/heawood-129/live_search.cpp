// Exact last-use search on a monotone row specification. Each input line is
// cap, positive count, negative count, signal count, and the truth words.
// A positive state limit is for exploration only. U means undecided.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
using State = std::vector<Word>;
struct Hash {
    std::size_t operator()(const State& xs) const {
        std::size_t h = 0xcbf29ce484222325ULL;
        for (Word x : xs) h = (h ^ x) * 0x100000001b3ULL;
        return h;
    }
};

template<int N> struct Bits {
    std::array<Word,N> v{};
    Bits operator|(const Bits& b) const {
        Bits r;
        for (int i=0;i<N;++i) r.v[i]=v[i]|b.v[i];
        return r;
    }
    bool operator==(const Bits& b) const {return v==b.v;}
};

template<int N> class Search {
    using Set=Bits<N>;
    int pos, neg, cap;
    std::size_t limit;
    Word target;
    Set full;
    State palette;
    std::unordered_map<Word,Set> covers;
    std::vector<std::unordered_set<State,Hash>> visited;
    std::size_t states=0, roots=0;
    char answer='N';

    Set cover(Word x) {
        auto it=covers.find(x);
        if (it!=covers.end()) return it->second;
        Set out;
        const Word zeros=((Word(1)<<neg)-1) & ~(x>>pos);
        for (int i=0;i<pos;++i) {
            if (!((x>>i)&1)) continue;
            int bit=i*neg, shift=bit%64, index=bit/64;
            out.v[index] |= zeros<<shift;
            if (shift && index+1<N) out.v[index+1] |= zeros>>(64-shift);
        }
        covers.emplace(x,out);
        return out;
    }

    void visit(const State& live,int k) {
        if (std::binary_search(live.begin(),live.end(),target)) {answer='Y';return;}
        if (!k || !visited[k].insert(live).second) return;
        if (++states>limit && limit) {answer='U';return;}
        const int n=static_cast<int>(live.size());
        // k gates can read at most k+1 distinct terminal labels.
        // Going to k-1 gates permits at most (k+1-n) retained operands.
        const int spare=k+1-n;
        std::vector<Set> cov(n),suffix(n+1);
        for (int i=n-1;i>=0;--i) {
            cov[i]=cover(live[i]);
            suffix[i]=suffix[i+1]|cov[i];
        }
        Set before;
        for (int i=0;i<n;++i) {
            Set others=before;
            for (int j=i+1;j<n;++j) {
                Set rest=others|suffix[j+1];
                for (Word z : {live[i]&live[j],live[i]|live[j]}) {
                    Set base=rest|cover(z);
                    for (int keep=0;keep<4;++keep) {
                        if (((keep&1)+((keep>>1)&1))>spare) continue;
                        Set visible=base;
                        if (keep&1) visible=visible|cov[i];
                        if (keep&2) visible=visible|cov[j];
                        if (!(visible==full)) continue;
                        State next;
                        next.reserve(n+1);
                        for (int h=0;h<n;++h)
                            if ((h!=i || (keep&1)) && (h!=j || (keep&2))) next.push_back(live[h]);
                        next.insert(std::lower_bound(next.begin(),next.end(),z),z);
                        visit(next,k-1);
                        if (answer!='N') return;
                    }
                }
                others=others|cov[j];
            }
            before=before|cov[i];
        }
    }

    void supports(const State& optional,std::size_t i,State& selected,Set current) {
        if (answer!='N') return;
        if (i==optional.size() || selected.size()==static_cast<std::size_t>(cap+1)) {
            if (current==full) {
                State root=selected;
                std::sort(root.begin(),root.end());
                ++roots;
                visit(root,cap);
            }
            return;
        }
        supports(optional,i+1,selected,current);
        selected.push_back(optional[i]);
        supports(optional,i+1,selected,current|cover(optional[i]));
        selected.pop_back();
    }

public:
    Search(int p,int n,int k,std::size_t l,State src)
      : pos(p),neg(n),cap(k),limit(l),target((Word(1)<<p)-1),palette(std::move(src)),visited(k+1) {
        for (int i=0;i<pos*neg;++i) full.v[i/64]|=Word(1)<<(i%64);
    }
    void run() {
        State forced,optional;
        Set start;
        for (std::size_t i=0;i<palette.size();++i) {
            Set others;
            for (std::size_t j=0;j<palette.size();++j) if (i!=j) others=others|cover(palette[j]);
            if (others==full) optional.push_back(palette[i]);
            else {forced.push_back(palette[i]);start=start|cover(palette[i]);}
        }
        if (forced.size()<=static_cast<std::size_t>(cap+1)) supports(optional,0,forced,start);
        std::cout<<answer<<' '<<states<<' '<<roots<<'\n'<<std::flush;
    }
};

int main(int argc,char** argv) {
    std::size_t limit=argc>1?std::stoull(argv[1]):0;
    int k,p,n,count;
    while (std::cin>>k>>p>>n>>count) {
        if (k<0 || k>30 || p<1 || n<1 || p+n>64 || count<1 || count>128)
            throw std::invalid_argument("unsupported instance size");
        State palette(count);
        for (auto& x:palette) if (!(std::cin>>x)) throw std::runtime_error("truncated input");
        int bits=p*n;
        if (bits<=64) Search<1>(p,n,k,limit,palette).run();
        else if (bits<=128) Search<2>(p,n,k,limit,palette).run();
        else if (bits<=256) Search<4>(p,n,k,limit,palette).run();
        else if (bits<=512) Search<8>(p,n,k,limit,palette).run();
        else if (bits<=1024) Search<16>(p,n,k,limit,palette).run();
        else throw std::invalid_argument("too many row pairs");
    }
}
