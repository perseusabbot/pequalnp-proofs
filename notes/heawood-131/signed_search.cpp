// Exhaustive last-use search for binary monotone circuits with signed restrictions.
// Read an instance reconstructed and validated by geometry131.py from standard input.
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
    Words palette;
};
struct Wire {
    Word column, fixed = 0, free = 0;
    Cover cover{};
};
struct StateHash {
    std::size_t operator()(const Words& key) const {
        Word hash = 0xcbf29ce484222325ULL;
        for (Word value : key) hash = (hash ^ value) * 0x100000001b3ULL;
        return hash;
    }
};
struct Gate { int a, b; bool isOr; Word result; };

class Search {
    int cap, positives, negatives, ports, testCount, blocks;
    Word positiveRows, negativeRows, everyTest;
    Cover wanted{};
    Words inputs;
    std::vector<Test> tests;
    std::unordered_map<Word,int> identifiers;
    std::vector<Wire> wires;
    std::vector<std::unordered_set<Words,StateHash>> visited;
    // An entry is the set of tests touching any row in this byte pattern.
    std::array<std::array<Word,256>,8> touching{};
    std::vector<Gate> prefix;
    Word expanded = 0, roots = 0;
    static constexpr std::size_t cacheLimit = 650000;

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
        int index = static_cast<int>(wires.size());
        identifiers.emplace(column,index);
        wires.push_back(wire);
        return index;
    }
    bool alreadySeen(const Wires& live, int left, const Rooms& room) {
        Words key(live.begin(),live.end());
        std::sort(key.begin(),key.end());
        for (int i = 0; i < testCount; i += 8) {
            Word packed = 0;
            for (int j = i; j < std::min(i+8,testCount); ++j) packed |= Word(room[j]) << (8*(j-i));
            key.push_back(packed);
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
    bool search(const Wires& live, int left, const Rooms& room) {
        for (int id : live) if (wires[id].column == positiveRows) return true;
        int n = static_cast<int>(live.size());
        if (!left || n < 2 || alreadySeen(live,left,room)) return false;
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
                        if (search(active,left-1,next)) return true;
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
            tests.push_back(t);
            Word selected = t.positive | t.negative;
            for (int byte = 0; byte < 8; ++byte, selected >>= 8)
                for (int pattern = 0; pattern < 256; ++pattern)
                    if (selected & pattern) touching[byte][pattern] |= Word(1) << i;
        }
        require(bool(std::cin), "Truncated input");
        std::string tail;
        require(!(std::cin >> tail), "Trailing input");
        for (int i = 0; i < ports; ++i) require(wireId(inputs[i]) == i, "Duplicate primary column");
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
            ++roots;
            if (search(live,cap,room)) { possible = true; break; }
        }
        std::cout << (possible ? "YES" : "NO") << ' ' << roots << ' ' << expanded << '\n';
        if (possible) for (const Gate& gate : prefix)
            std::cout << wires[gate.a].column << ' ' << wires[gate.b].column << ' '
                      << gate.isOr << ' ' << gate.result << '\n';
    }
};
int main() {
    try { Search s; s.read(); s.run(); }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
