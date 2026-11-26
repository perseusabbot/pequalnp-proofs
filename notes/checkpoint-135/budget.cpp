// Decide a weighted set-cover instance on a subgroup quotient.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
struct Mask {
    Word low, high;
    bool operator==(const Mask&) const = default;
    int count() const { return std::popcount(low)+std::popcount(high); }
    Mask remove(Mask m) const { return {low & ~m.low, high & ~m.high}; }
    int overlap(Mask m) const { return std::popcount(low & m.low)+std::popcount(high & m.high); }
    bool test(int i) const { return i < 64 ? (low >> i)&1 : (high >> (i-64))&1; }
};
struct Hash {
    std::size_t operator()(Mask m) const { return m.low ^ (m.high*0x9e3779b97f4a7c15ULL); }
};
struct Choice { int cost; Mask mask; };
struct Search {
    int n, budget;
    std::vector<Choice> choices;
    std::vector<std::vector<int>> at, available;
    std::vector<std::unordered_set<Mask,Hash>> failed;
    std::uint64_t nodes=0;

    bool solve(Mask need, int left) {
        const int size=need.count();
        if (!size) return true;
        if (!left || failed[left].contains(need)) return false;
        ++nodes;
        int pivot=-1;
        for (int i=0; i<n; ++i)
            if (need.test(i) && (pivot<0 || available[left][i]<available[left][pivot])) pivot=i;
        if (!available[left][pivot]) return false;
        std::array<int,16> gain{}, bound{};
        for (auto choice : choices) {
            if (choice.cost>left) break;
            gain[choice.cost]=std::max(gain[choice.cost],need.overlap(choice.mask));
        }
        // Even an unlimited supply of the maximum remaining gain at each
        // price must be able to cover all remaining cells.
        for (int i=1; i<=left; ++i)
            for (int c=1; c<=i; c*=2) bound[i]=std::max(bound[i],gain[c]+bound[i-c]);
        if (bound[left]>=size) {
            for (int idx : at[pivot]) {
                auto choice=choices[idx];
                if (choice.cost>left) break;
                Mask next=need.remove(choice.mask);
                if (next.count()<=bound[left-choice.cost] && solve(next,left-choice.cost)) return true;
            }
        }
        failed[left].insert(need);
        return false;
    }
    bool read() {
        int count;
        if (!(std::cin>>n>>budget>>count) || n<=0 || n>128 || budget<=0 || budget>15 || count<0) return false;
        choices.resize(count); at.resize(n); available.assign(budget+1,std::vector<int>(n)); failed.resize(budget+1);
        for (auto& choice : choices) {
            if (!(std::cin>>choice.cost>>choice.mask.low>>choice.mask.high) ||
                choice.cost<1 || choice.cost>budget || !std::has_single_bit(unsigned(choice.cost))) return false;
        }
        std::sort(choices.begin(),choices.end(),[](Choice a,Choice b) {
            if (a.cost!=b.cost) return a.cost<b.cost;
            return a.mask.count()>b.mask.count();
        });
        for (int j=0; j<count; ++j) {
            for (int i=0; i<n; ++i) if (choices[j].mask.test(i)) {
                at[i].push_back(j);
                for (int left=choices[j].cost; left<=budget; ++left) ++available[left][i];
            }
        }
        return true;
    }
};
int main() {
    Search solver;
    if (!solver.read()) return 1;
    auto lowBits=[](int n) { return n>=64 ? ~Word(0) : (Word(1)<<n)-1; };
    Mask full{lowBits(solver.n),lowBits(std::max(0,solver.n-64))};
    bool found=solver.solve(full,solver.budget);
    std::cout << (found ? "COVER" : "EXCLUDED") << ' ' << solver.nodes << '\n';
}
