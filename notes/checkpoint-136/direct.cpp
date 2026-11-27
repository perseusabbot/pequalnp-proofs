// Independently construct a rectangle-cover quotient from raw row subsets.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Shore = std::uint32_t;
constexpr int n = 21;
constexpr Shore all = (Shore{1} << n) - 1;
using Perm = std::array<int,2*n>;
using Footprint = std::pair<Word,Word>;  // high, low

static void check(bool condition, const char* reason) {
    if (!condition) throw std::runtime_error(reason);
}
static Word box(Shore a, Shore b) { return a | (Word(b) << n); }

struct Action {
    Perm p{};
    std::array<std::array<Word,256>,6> chunks{};
    explicit Action(Perm labels) : p(labels) {
        for (int q=0; q<6; ++q)
            for (int v=1; v<(1<<std::min(8,2*n-8*q)); ++v)
                chunks[q][v]=chunks[q][v&(v-1)] | (Word{1} << p[8*q+std::countr_zero(unsigned(v))]);
    }
    Word operator()(Word z) const {
        Word image=0;
        for (int q=0; q<6; ++q,z>>=8) image|=chunks[q][z&255];
        return image;
    }
    int cell(int i, int j) const {
        int a=p[i], b=p[n+j];
        if (a>=n) std::swap(a,b);
        return a*n+b-n;
    }
};

static int run() {
    int order;
    check(bool(std::cin>>order) && (order==4 || order==8 || order==16),"Unexpected group order");
    std::array<Shore,n> rows{},cols{};
    for (int i=0; i<n; ++i) {
        check(bool(std::cin>>rows[i]) && rows[i]<=all,"Invalid row");
        for (int j=0; j<n; ++j) if (rows[i]>>j&1u) cols[j]|=Shore{1}<<i;
    }
    std::vector<Action> group;
    std::set<Perm> elements;
    for (int t=0; t<order; ++t) {
        Perm p; Word seen=0;
        for (int& k:p) {
            check(bool(std::cin>>k) && k>=0 && k<2*n && !(seen>>k&1u),"Malformed permutation");
            seen|=Word{1}<<k;
        }
        for (int i=0; i<2*n; ++i)
            check((p[i]/n)==((p[0]/n)^(i/n)),"Map splits one axis");
        Action g(p);
        for (int i=0; i<n; ++i) for (int j=0; j<n; ++j) {
            int h=g.cell(i,j);
            check((rows[i]>>j&1u)==(rows[h/n]>>(h%n)&1u),"Map changes a board entry");
        }
        check(elements.insert(p).second,"Repeated group element");
        group.push_back(g);
    }
    for (const auto& g:group) for (const auto& h:group) {
        Perm k;
        for (int i=0; i<2*n; ++i) k[i]=g.p[h.p[i]];
        check(elements.contains(k),"Group is not closed");
    }
    std::array<int,n*n> index;
    index.fill(-1);
    int cells=0;
    for (int i=0; i<n; ++i) for (int j=0; j<n; ++j) {
        if (!(rows[i]>>j&1u) || index[n*i+j]>=0) continue;
        for (const auto& g:group) {
            int h=g.cell(i,j);
            check(index[h]==-1 || index[h]==cells,"Cell orbits overlap");
            index[h]=cells;
        }
        ++cells;
    }
    check(cells<=128,"Quotient exceeds 128 cells");
    std::vector<Shore> commonCols(all+1),commonRows(all+1);
    commonCols[0]=commonRows[0]=all;
    std::set<Word> candidates;
    Word legal=0;
    for (Shore a=1; a<=all; ++a) {
        int i=std::countr_zero(a);
        commonCols[a]=commonCols[a&(a-1)]&rows[i];
        commonRows[a]=commonRows[a&(a-1)]&cols[i];
    }
    for (Shore a=1; a<=all; ++a) {
        Shore common=commonCols[a];
        if (!common) continue;
        legal+=(Word{1}<<std::popcount(common))-1;
        if (commonRows[common]==a) candidates.insert(box(a,common));
        for (const auto& g:group) {
            if (g.p[0]<n) continue;
            Shore partner=g(a)>>n;
            if ((partner&~common)==0 && g(Word(partner)<<n)==a)
                candidates.insert(box(a,partner));
        }
    }
    check(legal==5833331,"Incorrect number of legal nonempty rectangles");
    std::map<Footprint,int> pool;
    auto footprint=[&](Word w) {
        Footprint result{};
        for (Shore a=w&all; a; a&=a-1) for (Shore b=w>>n; b; b&=b-1) {
            int id=index[n*std::countr_zero(a)+std::countr_zero(b)];
            check(id>=0,"Forbidden entry in candidate");
            (id>=64 ? result.first : result.second) |= Word{1}<<(id%64);
        }
        return result;
    };
    std::set<Word> visited;
    for (Word w:candidates) {
        if (visited.contains(w)) continue;
        std::set<Word> orbit;
        for (const auto& g:group) orbit.insert(g(w));
        Footprint m=footprint(w);
        for (Word z:orbit) {
            check(candidates.contains(z) && visited.insert(z).second,"Rectangle orbits do not partition candidates");
            check(footprint(z)==m,"Orbit members project to different cells");
        }
        int cost=static_cast<int>(orbit.size());
        if (cost>15) continue;
        auto [it,added]=pool.emplace(m,cost);
        if (!added) it->second=std::min(it->second,cost);
    }
    std::cout<<cells<<" 15 "<<pool.size()<<'\n';
    for (const auto& [m,c]:pool) std::cout<<c<<' '<<m.second<<' '<<m.first<<'\n';
    std::cerr<<legal<<' '<<candidates.size()<<'\n';
    return 0;
}

int main() {
    try { return run(); }
    catch (const std::exception& ex) { std::cerr<<ex.what()<<'\n'; return 1; }
}
