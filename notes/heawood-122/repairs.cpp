// Delete one tail gate, reroute reads of it, and replace one remaining tail gate.
// All 58 extremal assignments fit in a single word. Commutativity permits x <= y.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>
using Word = std::uint64_t;
constexpr int inputs = 14, zero = 63;
constexpr Word target = 2097151;
using Wires = std::array<Word, 64>;
struct Gate { int left, right; bool use_or; };
using Gates = std::vector<Gate>;

Word evaluate_gate(const Gate& g, const Wires& w) {
    return g.use_or ? w[g.left] | w[g.right] : w[g.left] & w[g.right];
}

Word replay(const Gates& gs, Wires w, int start, int removed, int alias, int output) {
    for (int g = start; g <= output; ++g)
        w[g] = g == removed ? w[alias] : evaluate_gate(gs[g], w);
    return w[output];
}

struct Result {
    Word schedules = 0, deletions = 0, replacements = 0, tested = 0, solutions = 0;
};

void search(const Gates& gs, const Wires& raw, Result& result) {
    int last = static_cast<int>(gs.size()) - 1;
    ++result.schedules;
    if (replay(gs, raw, inputs, -1, zero, last) != target)
        throw std::runtime_error("Original control does not compute the posted word");
    for (int removed = inputs + 2; removed <= last; ++removed) {
        int output = last - (removed == last);
        for (int a = 0; a <= removed; ++a) {
            if (removed == last && a != removed) continue; // no downstream read to redirect
            int alias = a == removed ? zero : a;
            ++result.deletions;
            Wires w = raw;
            for (int g = inputs; g <= output; ++g) {
                if (g == removed) {
                    w[g] = w[alias];
                    continue;
                }
                if (g >= inputs+2) {
                    // All out-of-range reads are represented by the one zero wire.
                    int available = g + 1 - (removed < g);
                    Word choices = static_cast<Word>(available) * (available + 1);
                    result.replacements += choices;
                    // For each input row the fixed downstream circuit is a monotone
                    // unary Boolean function of the replacement value.
                    w[g] = 0;
                    Word low = replay(gs, w, g+1, removed, alias, output);
                    w[g] = ~Word{0};
                    Word high = replay(gs, w, g+1, removed, alias, output);
                    if ((low & ~high) != 0) throw std::runtime_error("Nonmonotone suffix");
                    if ((low & ~target) == 0 && (target & ~high) == 0) {
                        result.tested += choices;
                        Word mask = high ^ low, wanted = target & mask;
                        for (int x = 0; x <= g; ++x) {
                            if (x == removed) continue;
                            Word left = w[x == g ? zero : x];
                            for (int y = x; y <= g; ++y) {
                                if (y == removed) continue;
                                Word right = w[y == g ? zero : y];
                                for (bool use_or : {false, true}) {
                                    Word val = use_or ? left | right : left & right;
                                    if ((val & mask) != wanted) continue;
                                    w[g] = val;
                                    if (replay(gs, w, g+1, removed, alias, output) != target)
                                        throw std::runtime_error("False positive in suffix shortcut");
                                    ++result.solutions;
                                }
                            }
                        }
                    }
                }
                w[g] = evaluate_gate(gs[g],w);
            }
        }
    }
}

int main() {
    Wires raw{};
    for (int i = 0; i < inputs; ++i)
        if (!(std::cin >> raw[i])) return EXIT_FAILURE;
    std::array<Result,65> results{};
    int index, n;
    while (std::cin >> index >> n) {
        if (index < 0 || index >= 65 || n < 3 || n + inputs >= zero) return EXIT_FAILURE;
        Gates gs(inputs);
        for (int i = 0, q; i < n; ++i) {
            if (!(std::cin >> q) || q < 0 || q >= 8192) return EXIT_FAILURE;
            int left = q%64, right = q/64%64;
            gs.push_back({left < i+inputs ? left : zero, right < i+inputs ? right : zero, q >= 4096});
        }
        search(gs,raw,results[index]);
    }
    for (int i=0; i<65; ++i) {
        const auto& r = results[i];
        if (r.schedules)
            std::cout << i << ' ' << r.schedules << ' ' << r.deletions << ' ' << r.replacements
                      << ' ' << r.tested << ' ' << r.solutions << '\n';
    }
}
