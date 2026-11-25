// Exhaustive last-use search for binary monotone circuits with signed restrictions.
// Input consists of signed restrictions followed by optional primary-input symmetries.
// Every supplied permutation is checked against the positive and negative row patterns.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
using Wires = std::vector<int>;
using Words = std::vector<Word>;
using Rooms = std::array<unsigned char, 64>;
using Cover = std::array<Word, 16>;

static Word lowBits(int n) { return n == 64 ? ~Word(0) : (Word(1) << n) - 1; }
static int sizeOf(Word set) { return __builtin_popcountll(set); }
static void require(bool valid, const char* message) {
    if (!valid) throw std::runtime_error(message);
}

struct Test {
    int floor;
    Word positive, negative;
    Words palette, one, two;
};
struct Wire {
    Word column, fixed = 0, free = 0;
    Cover cover{};
    std::array<int,64> weight{};
};
struct StateHash {
    std::size_t operator()(const Words& key) const {
        Word hash = 0xcbf29ce484222325ULL;
        for (Word value : key) hash = (hash ^ value) * 0x100000001b3ULL;
        return hash;
    }
};
struct Gate { int a, b; bool isOr; Word result; };

static bool coveredBy(Word need, const Words& covers) {
    for (Word c : covers) if (!(need & ~c)) return true;
    return false;
}
// These words mark rows where a substitute is allowed to differ in the signed direction.
static Words maximal(Words candidates, const Words& cheaper) {
    std::sort(candidates.begin(), candidates.end());
    candidates.erase(std::unique(candidates.begin(), candidates.end()), candidates.end());
    std::sort(candidates.begin(), candidates.end(), [](Word a, Word b) { return sizeOf(a) > sizeOf(b); });
    Words result;
    for (Word word : candidates)
        if (!coveredBy(word, cheaper) && !coveredBy(word, result)) result.push_back(word);
    return result;
}
static void localGates(Test& test) {
    Word selected = test.positive | test.negative;
    auto signedWord = [&](Word wire) { return (wire ^ test.negative) & selected; };
    Words free{test.positive, test.negative};
    for (Word primary : test.palette) free.push_back(signedWord(primary));
    Words one, two;
    for (Word a : test.palette) for (Word b : test.palette) {
        one.push_back(signedWord(a & b));
        one.push_back(signedWord(a | b));
    }
    test.one = maximal(std::move(one), free);
    for (Word a : test.palette) for (Word encoded : test.one) {
        Word b = encoded ^ test.negative;
        two.push_back(signedWord(a & b));
        two.push_back(signedWord(a | b));
    }
    free.insert(free.end(), test.one.begin(), test.one.end());
    test.two = maximal(std::move(two), free);
}
class Search {
    bool reference;
    int cap, positives, negatives, ports, testCount, blocks;
    Word positiveRows, negativeRows, everyTest;
    Cover wanted{};
    Words inputs;
    std::vector<Wires> permutations;
    std::vector<Test> tests;
    std::unordered_map<Word,int> identifiers;
    std::vector<Wire> wires;
    std::vector<std::unordered_set<Words,StateHash>> visited;
    // An entry is the set of tests touching any row in this byte pattern.
    std::array<std::array<Word,256>,8> touching{};
    std::vector<Gate> prefix;
    Word expanded = 0, roots = 0;
    std::size_t cacheLimit;

    Word violations(Word wantedColumn, Word replacement) const {
        return (wantedColumn & ~replacement & positiveRows) | (replacement & ~wantedColumn & negativeRows);
    }
    Word freeOn(Word column, Word replacement) const {
        Word delta = violations(column,replacement), failed = 0;
        for (int byte = 0; delta; ++byte, delta >>= 8) failed |= touching[byte][delta & 255];
        return everyTest & ~failed;
    }
    Cover joined(const Cover& a, const Cover& b) const {
        Cover result{};
        for (int i = 0; i < blocks; ++i) result[i] = a[i] | b[i];
        return result;
    }
    bool separates(const Cover& cover) const {
        for (int i = 0; i < blocks; ++i) if (cover[i] != wanted[i]) return false;
        return true;
    }
    int wireId(Word column) {
        auto found = identifiers.find(column);
        if (found != identifiers.end()) return found->second;
        Wire wire{column};
        Word absent = (negativeRows & ~column) >> positives;
        for (int i = 0; i < positives; ++i) {
            if (!(column & (Word(1) << i))) continue;
            int offset = i * negatives, block = offset / 64, shift = offset % 64;
            wire.cover[block] |= absent << shift;
            if (shift && block + 1 < blocks) wire.cover[block+1] |= absent >> (64-shift);
        }
        for (int i = 0; i < testCount; ++i) {
            const Test& test = tests[i];
            Word bit = Word(1) << i;
            if (!(column & test.positive) || !(~column & test.negative)) {
                wire.fixed |= bit;
                wire.free |= bit;
            } else {
                for (Word replacement : test.palette) {
                    if (!(violations(column,replacement) & (test.positive | test.negative))) {
                        wire.free |= bit;
                        break;
                    }
                }
            }
        }
        for (int i = 0; i < testCount; ++i) {
            const Test& test = tests[i];
            Word bit = Word(1) << i;
            if (wire.fixed & bit) {
                wire.weight[i] = -1;
            } else if (!(wire.free & bit)) {
                Word need = (column ^ test.negative) & (test.positive | test.negative);
                // A previously computed live wire can always be rebuilt from its prefix.
                wire.weight[i] = 512;
                if (coveredBy(need, test.one)) wire.weight[i] = 1;
                else if (coveredBy(need, test.two)) wire.weight[i] = 2;
            }
        }
        int index = static_cast<int>(wires.size());
        identifiers.emplace(column,index);
        wires.push_back(wire);
        return index;
    }
    // Equal live signatures at the same depth admit the same suffix.
    bool alreadySeen(const Wires& live, int left, const Rooms& room) {
        Words key(live.begin(),live.end());
        std::sort(key.begin(),key.end());
        if (reference) {
            for (int i = 0; i < testCount; i += 8) {
                Word packed = 0;
                for (int j = i; j < std::min(i+8,testCount); ++j) packed |= Word(room[j]) << (8*(j-i));
                key.push_back(packed);
            }
        }
        auto& table = visited[left];
        if (table.size() < cacheLimit) return !table.insert(std::move(key)).second;
        return table.find(key) != table.end();
    }
    bool globallyRedundant(Word column, const Wires& live) const {
        if (!(column & positiveRows) || !(~column & negativeRows)) return true;
        for (Word s : inputs) if (!violations(column,s)) return true;
        for (int id : live) if (!violations(column,wires[id].column)) return true;
        return false;
    }
    // room = cap - local floor - gates already saved - distinct live constants.
    bool update(Rooms& room, Word saved, Word fixed, Word removedA, Word removedB) const {
        Word changed = saved | fixed | removedA | removedB;
        while (changed) {
            int i = __builtin_ctzll(changed);
            Word bit = Word(1) << i;
            int charge = int(bool(saved & bit)) + int(bool(fixed & bit))
                       - int(bool(removedA & bit)) - int(bool(removedB & bit));
            int available = static_cast<int>(room[i]) - charge;
            if (available < 0) return false;
            require(available <= cap, "Inconsistent local budget");
            room[i] = static_cast<unsigned char>(available);
            changed ^= bit;
        }
        return true;
    }
    int moved(int id, int permutation) const {
        // The carried stabilizer fixes every gate already constructed.
        return id < ports ? permutations[permutation][id] : id;
    }
    std::pair<int,int> action(int a, int b, int permutation) const {
        int x = moved(a, permutation), y = moved(b, permutation);
        return {std::min(x,y), std::max(x,y)};
    }
    bool search(const Wires& live, int left, Rooms room, const Wires& group) {
        for (int id : live) if (wires[id].column == positiveRows) return true;
        int n = static_cast<int>(live.size());
        if (!left || n < 2 || alreadySeen(live,left,room)) return false;
        if (!reference) {
            std::array<int,64> sum{};
            for (int id : live)
                for (int j = 0; j < testCount; ++j) sum[j] += wires[id].weight[j];
            for (int j = 0; j < testCount; ++j) {
                int remaining = left - tests[j].floor + sum[j];
                if (remaining < 0) return false;
                if (remaining < room[j]) room[j] = static_cast<unsigned char>(remaining);
            }
        }
        ++expanded;
        std::vector<Cover> suffix(n+1,Cover{});
        for (int i = n-1; i >= 0; --i) suffix[i] = joined(wires[live[i]].cover,suffix[i+1]);
        Cover before{};
        for (int i = 0; i < n; ++i) {
            int a = live[i];
            Cover between = before;
            for (int j = i+1; j < n; ++j) {
                int b = live[j];
                Cover others = joined(between,suffix[j+1]);
                std::pair<int,int> pair = {std::min(a,b), std::max(a,b)};
                Wires fixing;
                bool primary = true;
                for (int perm : group) {
                    auto image = action(a,b,perm);
                    if (image < pair) { primary = false; break; }
                    if (image == pair) fixing.push_back(perm);
                }
                if (!primary) {
                    between = joined(between,wires[b].cover);
                    continue;
                }
                for (bool isOr : {false,true}) {
                    Word x = wires[a].column, y = wires[b].column;
                    Word z = isOr ? (x|y) : (x&y);
                    if (globallyRedundant(z,live)) continue;
                    int fresh = wireId(z);
                    Cover newCover = joined(others,wires[fresh].cover);
                    unsigned admissible = 0;
                    for (int keep = 0; keep < 4; ++keep) {
                        if (n-1 + sizeOf(keep) > left) continue;
                        Cover available = newCover;
                        if (keep & 1) available = joined(available,wires[a].cover);
                        if (keep & 2) available = joined(available,wires[b].cover);
                        if (separates(available)) admissible |= 1u << keep;
                    }
                    if (!admissible) continue;
                    Word saved = wires[fresh].free;
                    for (int old : live) {
                        if (saved == everyTest) break;
                        saved |= freeOn(z,wires[old].column);
                    }
                    for (int keep = 0; keep < 4; ++keep) {
                        if (!(admissible & (1u << keep))) continue;
                        Rooms next = room;
                        if (!update(next,saved,wires[fresh].fixed,keep&1 ? 0 : wires[a].fixed,
                                    keep&2 ? 0 : wires[b].fixed)) continue;
                        Wires active;
                        active.reserve(n+1);
                        for (int v = 0; v < n; ++v)
                            if ((v != i || (keep & 1)) && (v != j || (keep & 2))) active.push_back(live[v]);
                        active.push_back(fresh);
                        prefix.push_back({a,b,isOr,z});
                        Wires childGroup;
                        bool primaryKeep = true;
                        for (int p : fixing) {
                            if (moved(a,p) == b && (keep == 1 || keep == 2)) {
                                if (keep == 2) { primaryKeep = false; break; }
                            } else childGroup.push_back(p);
                        }
                        if (primaryKeep && search(active,left-1,next,childGroup)) return true;
                        prefix.pop_back();
                    }
                }
                between = joined(between,wires[b].cover);
            }
            before = joined(before,wires[a].cover);
        }
        return false;
    }

public:
    explicit Search(bool useReference)
        : reference(useReference), cacheLimit(useReference ? 350000 : 1300000) {}

    void read() {
        std::cin >> cap >> positives >> negatives >> ports >> testCount;
        require(std::cin && 0 <= cap && cap < 64 && 0 < positives && 0 < negatives &&
                positives + negatives <= 64 && positives * negatives <= 1024 &&
                0 < ports && ports <= 25 && 0 <= testCount && testCount <= 64, "Unsupported dimensions");
        positiveRows = lowBits(positives);
        negativeRows = lowBits(negatives) << positives;
        everyTest = lowBits(testCount);
        blocks = (positives*negatives+63)/64;
        for (int k = 0; k < positives*negatives; ++k) wanted[k/64] |= Word(1) << (k%64);
        inputs.resize(ports);
        for (Word& column : inputs) {
            std::cin >> column;
            require(!(column & ~(positiveRows|negativeRows)), "Invalid input column");
        }
        for (int i = 0; i < testCount; ++i) {
            Test t{};
            int count = 0;
            std::cin >> t.floor >> t.positive >> t.negative >> count;
            require(std::cin && t.floor >= 0 && t.positive && t.negative &&
                    !(t.positive & ~positiveRows) && !(t.negative & ~negativeRows) &&
                    count >= 0 && count <= 64, "Invalid local test");
            t.palette.resize(count);
            for (Word& p : t.palette) std::cin >> p;
            localGates(t);
            tests.push_back(t);
            Word selected = t.positive | t.negative;
            for (int byte = 0; byte < 8; ++byte, selected >>= 8)
                for (int pattern = 0; pattern < 256; ++pattern)
                    if (selected & pattern) touching[byte][pattern] |= Word(1) << i;
        }
        require(bool(std::cin), "Truncated input");
        Wires identity;
        for (int i = 0; i < ports; ++i) identity.push_back(i);
        std::cin >> std::ws;
        if (std::cin.peek() == std::char_traits<char>::eof()) {
            permutations.push_back(identity);
        } else {
            int order;
            require(bool(std::cin >> order) && order > 0 && order <= 336, "Invalid group size");
            for (int n = 0; n < order; ++n) {
                Wires permutation(ports);
                Word seen = 0;
                for (int& j : permutation) {
                    require(bool(std::cin >> j) && j >= 0 && j < ports && !(seen & (Word(1) << j)),
                            "Invalid permutation");
                    seen |= Word(1) << j;
                }
                permutations.push_back(permutation);
            }
            require(std::find(permutations.begin(), permutations.end(), identity) != permutations.end(),
                    "Missing identity");
            std::string tail;
            require(!(std::cin >> tail), "Trailing input");
        }
        for (const Wires& permutation : permutations) {
            for (int sign = 0; sign < 2; ++sign) {
                std::unordered_set<Word> original, image;
                int start = sign == 0 ? 0 : positives;
                int stop = sign == 0 ? positives : positives + negatives;
                for (int r = start; r < stop; ++r) {
                    Word old = 0, transformed = 0;
                    for (int i = 0; i < ports; ++i) if ((inputs[i] >> r) & 1) {
                        old |= Word(1) << i;
                        transformed |= Word(1) << permutation[i];
                    }
                    original.insert(old);
                    image.insert(transformed);
                }
                require(original == image, "Permutation changes signed rows");
            }
        }
        for (int i = 0; i < ports; ++i) {
            require(wireId(inputs[i]) == i, "Duplicate primary column");
            require(wires[i].free == everyTest, "Root primary costs gates on a restriction");
        }
        visited.resize(cap+1);
    }
    void run() {
        // If all other primaries fail one distinction, this primary must be in the output cone.
        Word mandatory = 0;
        for (int i = 0; i < ports; ++i) {
            Cover rest{};
            for (int j = 0; j < ports; ++j) if (j != i) rest = joined(rest,wires[j].cover);
            if (!separates(rest)) mandatory |= Word(1) << i;
        }
        bool possible = false;
        for (Word mask = mandatory; mask < (Word(1)<<ports); mask = (mask+1)|mandatory) {
            if (sizeOf(mask) > cap+1) continue;
            Wires live;
            Cover available{};
            for (int j = 0; j < ports; ++j) if (mask & (Word(1)<<j)) {
                live.push_back(j);
                available = joined(available,wires[j].cover);
            }
            if (!separates(available)) continue;
            Rooms room{};
            bool viable = true;
            for (int j = 0; j < testCount; ++j) {
                int initial = cap - tests[j].floor;
                for (int id : live) initial -= int((wires[id].fixed >> j) & 1);
                if (initial < 0) { viable = false; break; }
                room[j] = static_cast<unsigned char>(initial);
            }
            if (!viable) continue;
            Wires group;
            bool primary = true;
            for (int i = 0; i < static_cast<int>(permutations.size()); ++i) {
                Word image = 0;
                for (int id : live) image |= Word(1) << moved(id,i);
                if (image < mask) { primary = false; break; }
                if (image == mask) group.push_back(i);
            }
            if (!primary) continue;
            ++roots;
            if (search(live,cap,room,group)) { possible = true; break; }
        }
        std::cout << (possible ? "YES" : "NO") << ' ' << roots << ' ' << expanded << '\n';
        if (possible) for (const Gate& gate : prefix)
            std::cout << wires[gate.a].column << ' ' << wires[gate.b].column << ' '
                      << gate.isOr << ' ' << gate.result << '\n';
    }
};
int main(int argc, char** argv) {
    try {
        bool reference = argc == 2 && std::string(argv[1]) == "--reference";
        require(argc == 1 || reference, "Expected optional --reference");
        Search search(reference);
        search.read();
        search.run();
    }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
