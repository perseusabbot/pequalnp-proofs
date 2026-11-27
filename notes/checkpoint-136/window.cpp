// Color the incompatibility graph for a single retained subset, optionally leaving one vertex out.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Word=std::uint64_t;
constexpr int blocks=6;
struct Bits {
    std::array<Word,blocks> w{};
    bool has(int v) const {return (w[v/64]>>(v%64))&1;}
    void add(int v) {w[v/64]|=Word{1}<<(v%64);}
    void drop(int v) {w[v/64]&=~(Word{1}<<(v%64));}
    int first() const {
        for(int j=0;j<blocks;++j) if(w[j]) return 64*j+std::countr_zero(w[j]);
        return -1;
    }
    int size() const {int value=0;for(Word x:w)value+=std::popcount(x);return value;}
    Bits intersect(const Bits& other) const {
        Bits a;for(int j=0;j<blocks;++j)a.w[j]=w[j]&other.w[j];return a;
    }
    template<class F> void each(F f) const {
        for(int j=0;j<blocks;++j) for(Word x=w[j];x;x&=x-1) f(64*j+std::countr_zero(x));
    }
};
class Coloring {
    int k,n;
    std::vector<Bits> adj;
    std::vector<int> saturation;
    std::array<Bits,15> level;
    std::array<Bits,14> blocked;
    Bits free;
    std::vector<int> clique;
    Bits take(int v,int c) {
        level[saturation[v]].drop(v);free.drop(v);color[v]=c;
        Bits gain;
        if(c>=0) {
            for(int j=0;j<blocks;++j) {
                gain.w[j]=adj[v].w[j]&free.w[j]&~blocked[c].w[j];
                blocked[c].w[j]|=gain.w[j];
            }
            gain.each([&](int u){level[saturation[u]].drop(u);level[++saturation[u]].add(u);});
        }
        return gain;
    }
    void undo(int v,int c,const Bits& gain) {
        if(c>=0) {
            for(int j=0;j<blocks;++j) blocked[c].w[j]^=gain.w[j];
            gain.each([&](int u){level[saturation[u]].drop(u);level[--saturation[u]].add(u);});
        }
        level[saturation[v]].add(v);free.add(v);color[v]=-1;
    }
    bool search(int left,int used,bool hole) {
        if(!left) return true;
        ++states;
        int sat=k,v=level[k].first();
        if(v>=0 && (!hole || level[k].size()>1)) return false;
        while(v<0) v=level[--sat].first();
        for(int c=0;c<std::min(k,used+1);++c) {
            if(blocked[c].has(v)) continue;
            Bits changed=take(v,c);
            if(search(left-1,std::max(used,c+1),hole)) return true;
            undo(v,c,changed);
        }
        if(hole) {
            Bits changed=take(v,-2);
            if(search(left-1,used,false)) return true;
            undo(v,-2,changed);
        }
        return false;
    }
    bool start(int omitted,bool hole) {
        level={};blocked={};free={};
        saturation.assign(n,0);color.assign(n,-1);
        for(int i=0;i<n;++i) {level[0].add(i);free.add(i);}
        int used=0;
        for(int v:clique) {
            if(v==omitted) take(v,-2);
            else take(v,used++);
        }
        return search(n-int(clique.size()),used,hole);
    }
public:
    Word states=0;
    std::vector<int> color;
    Coloring(std::vector<Bits> graph,int limit):k(limit),n(graph.size()),adj(std::move(graph)) {
        if(n>336 || k<1 || k>14) throw std::runtime_error("Graph dimensions out of range");
        for(int first=0;first<n;++first) {
            std::vector<int> stack{first};
            Bits remaining=adj[first];
            while(remaining.first()>=0) {
                int best=-1,gain=-1;
                remaining.each([&](int v){
                    int d=remaining.intersect(adj[v]).size();
                    if(d>gain) {gain=d;best=v;}
                });
                stack.push_back(best);remaining=remaining.intersect(adj[best]);
            }
            if(stack.size()>clique.size()) clique=std::move(stack);
        }
    }
    bool solve(bool allowHole) {
        if(int(clique.size())>k+int(allowHole)) return false;
        if(int(clique.size())<=k && start(-1,allowHole)) return true;
        if(allowHole) for(int omitted:clique) if(start(omitted,false)) return true;
        return false;
    }
};
using Cell=std::pair<int,int>;
int main() {
    int n,originals,k,keep,hole;
    if(!(std::cin>>n>>originals>>k)||n!=21||originals!=14||k<1||k>14) return 1;
    std::array<unsigned,21> board;
    for(auto& w:board) if(!(std::cin>>w) || w>=(1u<<21)) return 1;
    std::array<std::pair<unsigned,unsigned>,14> seed;
    for(auto& [a,b]:seed) if(!(std::cin>>a>>b) || a>=(1u<<21)|| b>=(1u<<21)) return 1;
    if(!(std::cin>>keep>>hole)||keep<0||keep>=(1<<14)||std::popcount(unsigned(keep))+k!=14||(hole!=0 && hole!=1))return 1;
    std::vector<Cell> pts;
    for(int i=0;i<21;++i) {
        unsigned covered=0;
        for(int j=0;j<14;++j) if(keep>>j&1 && seed[j].first>>i&1u) covered|=seed[j].second;
        if(covered&~board[i]) return 1;
        for(unsigned w=board[i]&~covered;w;w&=w-1) pts.emplace_back(i,std::countr_zero(w));
    }
    auto conflict=[&](Cell a,Cell b) {return !(board[a.first]>>b.second & board[b.first]>>a.second & 1u);};
    std::vector<int> degree(pts.size()),indices(pts.size());
    for(unsigned i=0;i<pts.size();++i) for(unsigned j=0;j<i;++j)
        if(conflict(pts[i],pts[j])) {++degree[i];++degree[j];}
    std::iota(indices.begin(),indices.end(),0);
    std::stable_sort(indices.begin(),indices.end(),[&](int i,int j){return degree[i]>degree[j];});
    std::vector<Bits> adj(pts.size());
    for(unsigned i=0;i<pts.size();++i) for(unsigned j=0;j<i;++j)
        if(conflict(pts[indices[i]],pts[indices[j]])) {adj[i].add(j);adj[j].add(i);}
    Coloring solver(std::move(adj),k);
    bool found=solver.solve(hole);
    std::cout<<(found?"COVER":"EXCLUDED")<<' '<<keep<<' '<<solver.states<<'\n';
    if(found) {
        for(int i=0;i<14;++i) if(keep>>i&1) std::cout<<seed[i].first<<' '<<seed[i].second<<'\n';
        std::vector<std::pair<unsigned,unsigned>> replacements(k);
        for(unsigned i=0;i<pts.size();++i) if(solver.color[i]>=0) {
            auto [p,l]=pts[indices[i]];
            auto& [a,b]=replacements[solver.color[i]];a|=1u<<p;b|=1u<<l;
        }
        for(auto [a,b]:replacements) std::cout<<a<<' '<<b<<'\n';
    }
}
