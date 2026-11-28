// Cover a residual board with exactly the prescribed point and line degrees.
#pragma once
#include "board.hpp"
#include <functional>

struct Position {
    Residual target{};
    Margins slots{};
    Family available, selected;
    int left = 0;
};

struct Completion {
    const Board &board;
    Word nodes = 0;
    Family solution{};
    std::function<bool(const Family &)> onSolution;
    explicit Completion(const Board &b) : board(b) {}

    bool take(Position &pos, int j) const {
        if (!pos.left || !pos.available.has(j))
            return false;
        for (int i : board.membership[j])
            if (!pos.slots[i])
                return false;
        --pos.left;
        pos.available.erase(j);
        pos.selected.set(j);
        for (int i : board.membership[j]) {
            --pos.slots[i];
            pos.target[i] &= ~board.maximum[j].cover[i];
        }
        return true;
    }

    bool solve(Position pos) {
        ++nodes;
        for (int i = 0; i < 42; ++i) {
            const Site &s = board.sites[i];
            int q = pos.slots[i];
            if (q > pos.left || s.minimum[pos.target[i]] > q)
                return false;
            if (!q)
                pos.available = pos.available.without(s.through);
            else if (q == pos.left)
                pos.available = pos.available & s.through;
        }
        if (!pos.left) {
            solution = pos.selected;
            return onSolution ? onSolution(solution) : true;
        }
        Family pivot, forced;
        int width = 169;
        for (int i = 0; i < 42; ++i) {
            int q = pos.slots[i];
            if (!q)
                continue;
            Family options = pos.available & board.sites[i].through;
            int count = options.count();
            if (count < q)
                return false;
            if (count == q)
                for (int k = 0; k < 3; ++k)
                    forced.words[k] |= options.words[k];
            if (count < width) {
                width = count;
                pivot = options;
            }
        }
        for (int i = 0; i < 21; ++i)
            for (unsigned m = pos.target[i]; m; m &= m - 1) {
                Family options = pos.available & board.sites[i].entries[std::countr_zero(m)];
                int count = options.count();
                if (!count)
                    return false;
                if (count == 1)
                    for (int k = 0; k < 3; ++k)
                        forced.words[k] |= options.words[k];
                if (count < width) {
                    width = count;
                    pivot = options;
                }
            }
        if (forced.count()) {
            bool possible = true;
            forced.each([&](int j) {
                if (possible)
                    possible = take(pos, j);
            });
            return possible && solve(pos);
        }
        // At a label with one or two slots, branch on complete local choices when this is cheaper.
        std::vector<std::array<int, 2>> best;
        for (int i = 0; i < 42; ++i) {
            int q = pos.slots[i];
            if (q != 1 && q != 2)
                continue;
            const auto &site = board.sites[i];
            unsigned missing = pos.target[i];
            Family possible = pos.available & site.through;
            std::vector<std::array<int, 2>> candidates;
            if (q == 1) {
                Family choices = possible & site.singles[missing];
                int count = choices.count();
                if (!count)
                    return false;
                if (count >= width)
                    continue;
                choices.each([&](int j) { candidates.push_back({j, -1}); });
            } else {
                Family later = possible;
                possible.each([&](int j) {
                    later.erase(j);
                    if (int(candidates.size()) >= width)
                        return;
                    Family compatible = later & site.singles[missing & ~board.maximum[j].cover[i]];
                    compatible.each([&](int k) {
                        if (int(candidates.size()) < width)
                            candidates.push_back({j, k});
                    });
                });
                if (candidates.empty())
                    return false;
                if (int(candidates.size()) >= width)
                    continue;
            }
            width = candidates.size();
            best = std::move(candidates);
            if (width == 1)
                break;
        }
        if (!best.empty()) {
            for (auto [a, b] : best) {
                Position child = pos;
                if (take(child, a) && (b < 0 || take(child, b)) && solve(child))
                    return true;
            }
            return false;
        }
        bool found = false;
        pivot.each([&](int j) {
            if (found)
                return;
            Position child = pos;
            pos.available.erase(j);
            if (take(child, j))
                found = solve(child);
        });
        return found;
    }

    bool profile(int budget, const Margins &d, const Residual &target) {
        return solve(Position{target, d, board.all, {}, budget});
    }
};
