// Exact cover feasibility at a fixed budget, split by the numbers of orbit sizes.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_set>
#include <unordered_map>
#include <numeric>
#include <vector>

using Word=std::uint64_t;
struct Mask {
    Word low,high;
    bool operator==(const Mask&) const=default;
    int size() const {return std::popcount(low)+std::popcount(high);}
    Mask minus(Mask b) const {return {low&~b.low,high&~b.high};}
    bool within(Mask b) const {return !(low&~b.low) && !(high&~b.high);}
    int overlap(Mask b) const {return std::popcount(low&b.low)+std::popcount(high&b.high);}
    template<class F> void cells(F apply) const {
        for (auto v=low; v; v&=v-1) apply(std::countr_zero(v));
        for (auto v=high; v; v&=v-1) apply(64+std::countr_zero(v));
    }
};
struct Hash { std::size_t operator()(Mask m) const {return m.low^(m.high*0x9e3779b97f4a7c15ULL);} };
using Counts=std::array<int,4>;

struct Weight {
    Counts maxima{};
    std::vector<std::array<int,256>> lookup;
    int value(Mask m) const {
        int sum=0;
        for (unsigned i=0; i<lookup.size(); ++i) {
            Word& v=i<8?m.low:m.high;
            sum+=lookup[i][v&255];v>>=8;
        }
        return sum;
    }
};
struct ProfileCover {
    int n,cap,profileCount=0;
    Mask full;
    std::array<std::vector<Mask>,4> words;
    std::array<std::array<std::vector<Mask>,128>,4> postings;
    std::vector<Weight> weights;
    std::vector<std::array<std::vector<int>,4>> images;
    std::array<std::vector<int>,4> domainIds;
    std::array<std::unordered_set<Mask,Hash>,1024> failed;
    std::vector<int> activeWeights;
    std::array<std::vector<std::vector<int>>,4> pairLists;
    Word states=0;
    std::vector<std::pair<int,Mask>> witness;
    static int key(Counts r) {return r[0]+16*r[1]+128*r[2]+512*r[3];}
    static Word lowBits(int s) {return s>=64 ? ~Word(0) : (Word(1)<<s)-1;}

    void read() {
        int items;
        if (!(std::cin>>n>>cap>>items) || n<1||n>128||cap<1||cap>15||items<1)
            throw std::runtime_error("Invalid board or budget");
        full={lowBits(std::min(64,n)),lowBits(std::max(0,n-64))};
        for(int i=0; i<items; ++i) {
            int cost; Mask m;
            if (!(std::cin>>cost>>m.low>>m.high) || cost<1 || cost>8 || !std::has_single_bit(unsigned(cost)) || !m.within(full))
                throw std::runtime_error("Invalid candidate");
            words[std::countr_zero(unsigned(cost))].push_back(m);
        }
        for (int c=0; c<4; ++c) {
            // A containing mask at the same price can always replace a smaller one.
            auto& choices=words[c];
            std::sort(choices.begin(),choices.end(),[](Mask a,Mask b) {
                if (a.size()!=b.size()) return a.size()>b.size();
                if (a.high!=b.high) return a.high<b.high;
                return a.low<b.low;
            });
            std::vector<Mask> kept;
            for (Mask m:choices) {
                if (std::any_of(kept.begin(),kept.end(),[m](Mask v){return m.within(v);})) continue;
                kept.push_back(m);
                m.cells([&](int j){postings[c][j].push_back(m);});
            }
            choices=std::move(kept);
        }
        int count;
        if (!(std::cin>>count) || count<0 || count>10000) throw std::runtime_error("Invalid weights");
        for (int w=0; w<count; ++w) {
            std::array<int,128> direct{};
            for (int i=0; i<n; ++i)
                if (!(std::cin>>direct[i]) || direct[i]<0 || direct[i]>1000000)
                    throw std::runtime_error("Weight outside integer range");
            Weight weight; weight.lookup.resize((n+7)/8);
            for (int i=0; i<(n+7)/8; ++i) {
                auto& t=weight.lookup[i]; t[0]=0;
                for (unsigned j=1; j<256; ++j) t[j]=t[j&(j-1)]+direct[8*i+std::countr_zero(j)];
            }
            for (int c=0; c<4; ++c)
                for(Mask m:words[c]) weight.maxima[c]=std::max(weight.maxima[c],weight.value(m));
            weights.push_back(std::move(weight));
        }
        if (words[0].empty()) throw std::runtime_error("Padding to the budget requires a fixed rectangle");
        int symmetryCount=0;
        std::cin>>std::ws;
        if(std::cin.peek()!=std::char_traits<char>::eof() && !(std::cin>>symmetryCount))
            throw std::runtime_error("Invalid symmetry list");
        if(symmetryCount<0 || symmetryCount>4096) throw std::runtime_error("Unexpected symmetry count");
        std::array<std::unordered_map<Mask,int,Hash>,4> index;
        for(int c=0;c<4;++c) for(unsigned j=0;j<words[c].size();++j) index[c].emplace(words[c][j],j);
        for(int i=0;i<symmetryCount;++i) {
            std::vector<int> perm(n);std::vector<bool> used(n);
            for(int& v:perm) {
                if(!(std::cin>>v) || v<0 || v>=n || used[v]) throw std::runtime_error("Invalid cell permutation");
                used[v]=true;
            }
            std::array<std::vector<int>,4> action;
            for(int c=0;c<4;++c) for(Mask m:words[c]) {
                Mask z{};
                m.cells([&](int j){
                    int v=perm[j]; (v<64?z.low:z.high)|=Word{1}<<(v%64);
                });
                auto hit=index[c].find(z);
                if(hit==index[c].end()) throw std::runtime_error("Symmetry changes a same-price mask");
                action[c].push_back(hit->second);
            }
            images.push_back(std::move(action));
        }
    }
    bool one(Mask need,int c) {
        if (!need.size()) return true;
        int first=-1,second=-1;
        need.cells([&](int i){
            if(first<0 || postings[c][i].size()<postings[c][first].size()) {
                second=first;first=i;
            } else if(second<0 || postings[c][i].size()<postings[c][second].size()) second=i;
        });
        if(second<0) {
            if(postings[c][first].empty()) return false;
            witness.emplace_back(1<<c,postings[c][first].front());return true;
        }
        for(int i:pairLists[c][std::min(first,second)*n+std::max(first,second)]) {
            Mask m=words[c][i];
            if(need.within(m)) {witness.emplace_back(1<<c,m);return true;}
        }
        return false;
    }
    bool solve(Mask need,Counts slots) {
        if (!need.size()) return true;
        int count=0;
        for (int c=0;c<4;++c) count+=slots[c];
        if (!count) return false;
        if (count==1) {
            for (int c=0;c<4;++c) if (slots[c]) return one(need,c);
        }
        auto& seen=failed[key(slots)];
        if (seen.contains(need)) return false;
        ++states;
        for (int id:activeWeights) {
            const auto& w=weights[id];
            int capacity=0;
            for (int c=0;c<4;++c) capacity+=slots[c]*w.maxima[c];
            if(w.value(need)>capacity) return false;
        }
        const int size=need.size();
        int price=-1, pivot=-1;
        std::size_t best=std::numeric_limits<std::size_t>::max();
        for (int c=0;c<4;++c) if(slots[c] && words[c].size()<best) {
            price=c;best=words[c].size();
        }
        need.cells([&](int i){
            std::size_t length=0;
            for(int c=0;c<4;++c) if(slots[c]) length+=postings[c][i].size();
            if(length<best) {pivot=i;best=length;}
        });
        std::size_t meanCount=0;
        if(count<=3) for(int c=0;c<4;++c) if(slots[c]) {
            const auto& choices=words[c];
            meanCount+=std::partition_point(choices.begin(),choices.end(),[&](Mask m){return m.size()*count>=size;})-choices.begin();
        }
        if (count<=3 && meanCount<best) {
            // A solution has a rectangle meeting at least the average remaining demand.
            for (int c=0;c<4;++c) if (slots[c]) {
                Counts left=slots;--left[c];
                for (Mask m:words[c]) {
                    if (m.size()*count<size) break;
                    if (m.overlap(need)*count>=size && solve(need.minus(m),left)) {
                        witness.emplace_back(1<<c,m);return true;
                    }
                }
            }
        } else if (pivot>=0) {
            for (int c=0;c<4;++c) if (slots[c]) {
                Counts left=slots;--left[c];
                for (Mask m:postings[c][pivot])
                    if (solve(need.minus(m),left)) {witness.emplace_back(1<<c,m);return true;}
            }
        } else {
            Counts left=slots;--left[price];bool hits=false;
            for (Mask m:words[price]) if (m.overlap(need)) {
                hits=true;
                if (solve(need.minus(m),left)) {witness.emplace_back(1<<price,m);return true;}
            }
            if (!hits && solve(need,left)) return true;
        }
        if(seen.size()<500000) seen.insert(need);
        return false;
    }
    // For each cost profile, discard masks that already spend more than its
    // slack for some integer weight. A tighter domain gives tighter maxima.
    bool restrictDomains(Counts slots, const std::array<std::vector<Mask>,4>& allWords,
                         const std::vector<std::array<std::vector<int>,4>>& values) {
        std::array<std::vector<int>,4> ids;
        for (int c=0;c<4;++c) if (slots[c])
            for (int j=0;j<static_cast<int>(allWords[c].size());++j) ids[c].push_back(j);
        bool changed;
        do {
            changed=false;
            std::array<Mask,4> united{};
            for (int c=0;c<4;++c) {
                if (slots[c] && ids[c].empty()) return false;
                for (int j:ids[c]) {
                    united[c].low |= allWords[c][j].low;
                    united[c].high |= allWords[c][j].high;
                }
            }
            Mask missing=full;
            for (Mask m:united) missing=missing.minus(m);
            if (missing.size()) return false;
            for (int c=0;c<4;++c) if (slots[c]==1) {
                Mask exclusive=full;
                for (int other=0;other<4;++other) if(other!=c) exclusive=exclusive.minus(united[other]);
                changed |= std::erase_if(ids[c],[&](int j){return !exclusive.within(allWords[c][j]);})!=0;
            }
            for (unsigned k=0;k<weights.size();++k) {
                auto& w=weights[k];
                int capacity=0;
                for (int c=0;c<4;++c) {
                    int best=0;
                    for (int j:ids[c]) best=std::max(best,values[k][c][j]);
                    w.maxima[c]=best;capacity+=slots[c]*best;
                }
                int slack=capacity-w.value(full);
                if (slack<0) return false;
                for (int c=0;c<4;++c) if (slots[c]) {
                    int threshold=w.maxima[c]-slack;
                    if (threshold>0)
                        changed |= std::erase_if(ids[c],[&](int j){return values[k][c][j]<threshold;})!=0;
                }
            }
        } while(changed);
        domainIds=ids;
        for (int c=0;c<4;++c) {
            words[c].clear();
            for (int i=0;i<n;++i) postings[c][i].clear();
            for (int j:ids[c]) {
                Mask m=allWords[c][j];words[c].push_back(m);
                m.cells([&](int i){postings[c][i].push_back(m);});
            }
        }
        return true;
    }
    // Small relative slack gives useful cuts. All bounds remain necessary,
    // regardless of which are selected. Cross-products fit in signed 64 bits
    // at the input limits of 128 cells, 15 slots and weights no larger than 10^6.
    std::vector<int> rankedWeights(Mask target, Counts slots, unsigned limit) const {
        struct Score { int id; long long capacity; int demand; };
        std::vector<Score> scores;
        for(unsigned k=0;k<weights.size();++k) {
            int demand=weights[k].value(target);
            if(!demand) continue;
            long long capacity=0;
            for(int c=0;c<4;++c) capacity+=1LL*slots[c]*weights[k].maxima[c];
            scores.push_back({static_cast<int>(k),capacity,demand});
        }
        std::stable_sort(scores.begin(),scores.end(),[](Score a,Score b){
            return a.capacity*b.demand<b.capacity*a.demand;
        });
        if(scores.size()>limit) scores.resize(limit);
        std::vector<int> selected;
        for(Score s:scores) selected.push_back(s.id);
        return selected;
    }
    void prepareTerminal(Counts slots) {
        activeWeights=rankedWeights(full,slots,16);
        for(int c=0;c<4;++c) {
            auto& pairs=pairLists[c];pairs.assign(n*n,{});
            for(unsigned j=0;j<words[c].size();++j) {
                Mask mask=words[c][j];
                mask.cells([&](int a){mask.cells([&](int b){if(a<b) pairs[a*n+b].push_back(j);});});
            }
        }
    }
    bool conditioned(Mask need, Counts slots) {
        int count=std::accumulate(slots.begin(),slots.end(),0);
        if(count<=3 || !need.size()) return solve(need,slots);
        // On each normalized prefix, overlapping cells already paid for cannot
        // contribute to a weight bound on the remaining cells.
        ProfileCover child;
        child.n=n;child.full=need;
        for(int id:rankedWeights(need,slots,32)) child.weights.push_back(weights[id]);
        std::array<Mask,4> united{};
        for(int c=0;c<4;++c) for(Mask m:words[c]) {
            united[c].low|=m.low;united[c].high|=m.high;
        }
        std::vector<Mask> boundaries;
        for(int unavailable=0;unavailable<16;++unavailable) {
            Mask boundary=need;
            for(int c=0;c<4;++c) if(unavailable>>c&1) boundary=boundary.minus(united[c]);
            if(!boundary.size() || std::find(boundaries.begin(),boundaries.end(),boundary)!=boundaries.end()) continue;
            boundaries.push_back(boundary);Weight w;w.lookup.resize((n+7)/8);
            for(int i=0;i<(n+7)/8;++i) {
                unsigned segment=((i<8?boundary.low:boundary.high)>>(8*(i%8)))&255;
                for(unsigned v=0;v<256;++v) w.lookup[i][v]=std::popcount(v&segment);
            }
            child.weights.push_back(std::move(w));
        }
        std::vector<std::array<std::vector<int>,4>> values(child.weights.size());
        for(unsigned k=0;k<child.weights.size();++k)
            for(int c=0;c<4;++c) if(slots[c])
                for(Mask m:words[c]) values[k][c].push_back(child.weights[k].value({m.low&need.low,m.high&need.high}));
        if(!child.restrictDomains(slots,words,values)) return false;
        child.prepareTerminal(slots);
        bool result=child.solve(need,slots);
        states+=child.states;
        if(result) witness.insert(witness.end(),child.witness.begin(),child.witness.end());
        return result;
    }
    bool normalized(Mask need,Counts slots,const std::vector<int>& fixing,int depth) {
        int count=std::accumulate(slots.begin(),slots.end(),0);
        if(!depth || fixing.size()<2 || count<=3 || !need.size()) return conditioned(need,slots);
        int chosen=-1;
        std::vector<int> leaders;
        const int total=need.size();
        for(int c=0;c<4;++c) if(slots[c]) {
            std::vector<int> candidates;
            for(unsigned j=0;j<words[c].size();++j) {
                if(slots[c]==count && count*need.overlap(words[c][j])<total) continue;
                int id=domainIds[c][j];
                bool first=std::none_of(fixing.begin(),fixing.end(),[&](int h){return images[h][c][id]<id;});
                if(first) candidates.push_back(j);
            }
            // A single non-unit slot often becomes much easier to check once
            // chosen explicitly, since that price disappears from the residual.
            bool preferred=slots[c]==1 && c>=1;
            bool oldPreferred=chosen>=0 && slots[chosen]==1 && chosen>=1;
            if(chosen<0 || (preferred && !oldPreferred) || (preferred==oldPreferred && candidates.size()<leaders.size())) {
                chosen=c;leaders=std::move(candidates);
            }
        }
        // Every image of a solution survives the necessary weight cuts. Choose
        // a minimal image of one slot of this price, then retain maps fixing it.
        --slots[chosen];
        for(int j:leaders) {
            std::vector<int> next;
            int id=domainIds[chosen][j];
            for(int h:fixing) if(images[h][chosen][id]==id) next.push_back(h);
            Mask m=words[chosen][j];
            if(normalized(need.minus(m),slots,next,depth-1)) {
                witness.emplace_back(1<<chosen,m);return true;
            }
        }
        return false;
    }
    bool run() {
        const auto allWords=words;
        std::vector<int> group(images.size());std::iota(group.begin(),group.end(),0);
        std::vector<std::array<std::vector<int>,4>> values(weights.size());
        for (unsigned k=0;k<weights.size();++k)
            for(int c=0;c<4;++c)
                for(Mask m:allWords[c]) values[k][c].push_back(weights[k].value(m));
        for(int h=0;h<=cap/8;++h) for(int q=0;q<=(cap-8*h)/4;++q)
            for(int p=0;p<=(cap-8*h-4*q)/2;++p) {
                Counts slots{cap-8*h-4*q-2*p,p,q,h};
                bool available=true;
                for(int c=0;c<4;++c) if(slots[c] && allWords[c].empty()) available=false;
                if(!available) continue;
                ++profileCount;
                if(!restrictDomains(slots,allWords,values)) continue;
                prepareTerminal(slots);
                // A failed residual is specific to this profile's surviving masks.
                for(auto& cache:failed) cache.clear();
                if(normalized(full,slots,group,2)) return true;
            }
        return false;
    }
};
int main() {
    try {
        ProfileCover search;search.read();bool yes=search.run();
        std::cout<<(yes?"COVER":"EXCLUDED")<<' '<<search.profileCount<<' '<<search.states<<'\n';
        if(yes) for(const auto& [cost,mask]:search.witness)
            std::cout<<cost<<' '<<mask.low<<' '<<mask.high<<'\n';
    } catch(const std::exception& e) {std::cerr<<e.what()<<'\n';return 1;}
}
