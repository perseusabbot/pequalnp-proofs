// Independent count by scanning every nonempty set of rows of this 21 by 21 matrix.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>

using Mask = std::uint32_t;
using Signature = std::uint64_t;

int main() {
    constexpr unsigned n = 21;
    constexpr Mask all = (1u << n) - 1;
    // The five 1-entries of row 0, rotated left by the row index.
    constexpr Mask first = (1u << 0) | (1u << 5) | (1u << 7) | (1u << 17) | (1u << 20);
    const auto shift = [&](Mask m, unsigned k) {
        return ((m << k) | (m >> (n - k))) & all;
    };
    std::vector<Mask> rows(n);
    for (unsigned i = 0; i < n; ++i)
        rows[i] = all ^ shift(first, i);

    std::vector<Mask> common(1u << n, all);
    std::set<Mask> columnSets;
    for (Mask a = 1; a <= all; ++a) {
        common[a] = common[a & (a - 1)] & rows[std::countr_zero(a)];
        if (common[a]) columnSets.insert(common[a]);
    }
    std::set<Signature> signatures;
    std::set<std::pair<Mask, Mask>> orbits;
    for (Mask b : columnSets) {
        Mask a = 0;
        for (unsigned i = 0; i < n; ++i)
            if ((rows[i] & b) == b) a |= 1u << i;
        auto representative = std::make_pair(a,b);
        for (unsigned k = 3; k < n; k += 3)
            representative = std::min(representative, {shift(a,k),shift(b,k)});
        if (!orbits.insert(representative).second) continue;

        Signature s = 0;
        unsigned index = 0;
        for (unsigned i = 0; i < 3; ++i)
            for (unsigned j = 0; j < n; ++j) {
                if (!(rows[i] & (1u << j))) continue;
                for (unsigned k = 0; k < n; k += 3)
                    if (((a >> ((i+k)%n)) & (b >> ((j+k)%n))) & 1u)
                        s |= Signature{1} << index;
                ++index;
            }
        if (index != 48) return 1;
        signatures.insert(s);
    }
    std::vector<Signature> words(signatures.begin(),signatures.end());
    std::vector<unsigned> histogram(49);
    std::uint64_t pairs = 0;
    for (std::size_t i = 0; i < words.size(); ++i)
        for (std::size_t j = 0; j <= i; ++j) {
            ++histogram[std::popcount(words[i] | words[j])];
            ++pairs;
        }
    std::cout << columnSets.size() << ' ' << orbits.size() << ' ' << words.size() << ' ' << pairs << '\n';
    for (unsigned i = 0; i < histogram.size(); ++i)
        if (histogram[i]) std::cout << i << ' ' << histogram[i] << '\n';
}
