# Checkpoint 136 · How many symmetries could a small cover have?

Any complete cover of the 336 zeros using **13 or 14 rectangles** would have either **120,960 or 241,920 distinct images** under board symmetry. At most two symmetries could fix its rectangle family. For a cover of size 15, the number of images is divisible by **20,160**, so at most 12 symmetries can fix the family.

The unrestricted minimum on this 21 × 21 board remains between **13 and 15**. Jonathan Chassot (JLDC) proved that 12 rectangles cannot suffice. DPS0340 constructed a cover using 15. Whether 13 or 14 suffice remains open on the project desk. [Lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [Upper bound](https://github.com/open-goat/pequalnp-proofs/pull/13338) · [Project desk](https://data.pequalnp.com/data/desk/gaps.json)

## Counting all board symmetries

A symmetry permutes row labels and column labels while preserving all 441 entries. It may also interchange the two sides. Fix the images of rows 0 through 4 in order. For a symmetry preserving the two sides, the numbers of choices at the successive steps are **21, 20, 16, 9 and 2**. A line is determined by two incident points, and a point by two incident lines. Starting with the five rows, 37 applications of these two operations recover all 42 labels. A side-preserving symmetry fixing those rows fixes the board pointwise.

Lean checks that words in the three explicit generators attain every choice at each step. Consequently there are exactly **120,960** side-preserving symmetries, and these generators produce all of them. Composition with one explicit polarity pairs them with all 120,960 side-exchanging symmetries. This proves the group of **241,920** used in the previous checkpoint is the full group for these actions. [Frame and group proofs](src/Frames.lean) · [Certificate generator](frames.py)

## Testing invariant covers

A legal rectangle is a nonempty product of rows and columns containing only zeros. A symmetry fixes a family when it permutes the rectangles as a set. Choose a subgroup of order 256, the full power of two dividing 241,920. Every subgroup of order four or eight in the board group has a conjugate in this subgroup.

| Subgroup order | Subgroups inside the group of order 256 | Classes in the full board group | Subgroups in the full board group | Classes excluded at size 13 | At size 14 | At size 15 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 191 | 9 | 30,975 | 9 | 9 | — |
| 8 | 271 | 26 | 89,775 | 26 | 26 | 26 |

The dash marks a budget outside the order-four calculation. Of the 271 subgroups of order eight in the chosen group of order 256, 159 preserve the two sides and 112 include a map exchanging them. They give 12 and 14 classes respectively under conjugation by the full board group. The program builds the subgroup lists twice, first by adjoining elements and then by descending through subgroups of index two. It counts conjugates from the normalizers in the full group. [Subgroup enumeration](subgroups.py) · [Per-class counts and decisions](results.json)

An invariant family is a union of rectangle orbits. Each orbit costs its number of rectangles and covers a set of cell orbits. If every symmetry stabilizing a rectangle preserves the axes, extending that rectangle to a maximal legal rectangle gives an orbit of at most the original cost. If a side-exchanging symmetry fixes the rectangle, the candidate list retains it directly. Thus the search includes the 25,235 maximal legal rectangles and every additional legal rectangle fixed by a side-exchanging subgroup element. Lean proves the extension, containment and orbit-cost implications. [Rectangle orbit proofs](src/RectangleOrbits.lean)

One quotient constructor uses the maximal rectangles and cliques of compatible rows for each side exchange. A second constructor scans all nonempty row sets, counts all **5,833,331** nonempty legal rectangles by their column subsets, and tests for maximality or a side-exchanging stabilizer. For every representative the two constructors produce byte-identical lists of costs and covered cell orbits. [First constructor](subgroups.py) · [Independent constructor](direct.cpp)

The exact search enumerates the possible counts of orbits costing 1, 2, 4 or 8. A spare slot can be filled by a fixed rectangle, so testing the stated budget also rules out every smaller one. Containment at the same price discards dominated choices. Nonnegative integer weights bound how much of the board each remaining slot can cover. The checker recomputes these inequalities directly from the rectangle masks. The normalizer gives permutations of the cell orbits that the checker validates on the same-price masks. They allow the first two choices to use representatives. Fixing an orbit removes its already covered cells from the remaining weight bounds. The search then branches on a price, an uncovered cell or a rectangle covering at least the average remaining demand. It returns a footprint witness if the budget succeeds. Small instances with asymmetric weights are compared with exact minima from a separate subset calculation. A second exact solver using the previously published cost search separately excludes all 26 order-eight cases at budget 15. [Profile search](profiles.cpp) · [Independent solver](../checkpoint-135/budget.cpp) · [Integer weights](weights.json)

For size 13, excluding every subgroup of order four forces the power of two in a family stabilizer to divide two. For size 15, excluding every subgroup of order eight forces it to divide four. The odd orbit divisors from Checkpoint 135 are 945 through size 14 and 315 at size 15. Combining the odd and even factors gives the following constraints. [Finite-group deductions](src/OrbitBounds.lean) · [Odd-prime exclusions](../checkpoint-135/README.md)

| Number of rectangles | Divisor of the number of distinct images | Maximum number of symmetries fixing a family |
| ---: | ---: | ---: |
| 13 | 120,960 | 2 |
| 14 | 120,960 | 2 |
| 15 | 20,160 | 12 |

## How far the 334-cell example can be repaired

The published 14-rectangle example misses two of the 336 zeros. Both repair searches pending at Checkpoint 135 finished. Each gives the replacement rectangles freedom to cover any legal cells on the board, including zeros in the retained rectangles.

| Retained original rectangles | Target zeros covered with at most 14 | Choices exhausted | Coloring search states | Distinct retained sets excluded after all symmetries |
| ---: | ---: | ---: | ---: | ---: |
| 5 | 336 | 2,002 | 20,546,859,847 | 225,106,560 |
| 6 | At least 335 | 3,003 | 10,107,878,558 | 353,283,840 |

The five-rectangle choices occupy 962 symmetry orbits and the six-rectangle choices occupy 1,500. Orbit–stabilizer and a second count by the number of maps returning each set to the example give the same totals. The largest individual coloring cases required 69,279,625 and 63,476,866 states, respectively. A separate SAT encoding checks one selected residual from each completed search. Each pair of cells placed in the same rectangle must have both crossed cells legal on the original board, even when a zero may be omitted. [Repair receipts](repair-runs.json) · [Independent coloring encoding and orbit counts](repairs.py) · [Original family](../checkpoint-133/plane-examples.json)

Two larger computations have resumable drivers. One tests whether retaining five rectangles from this example still allows 335 covered zeros. Its 962 symmetry representatives are written to a journal as they finish. The other resumes the 22-gate Heawood reduced search from Checkpoint 132. Its prior run was interrupted before delivering a decision. Its 94 disjoint first-gate branches now have separate receipts. The first completed branch was excluded after 67,003,246 search states. The fork includes portable copies of the completed cases for both searches. The cumulative archive also records their live progress at its save time. [Saved rectangle decisions](resume/near-nine/decisions.json) · [Saved Heawood decisions](resume/heawood/completed) [Rectangle driver](windows.py) · [Heawood driver](heawood.py) · [Heawood reduction](../heawood-132/README.md)

## Reproducing the checkpoint

From this directory, Python 3.10 or later and a C++20 compiler rebuild the subgroup inventories, both quotient constructions, the reported decisions, and the frame certificate. The optional SAT check uses CaDiCaL.

```sh
python3 -B verify.py --jobs 2 --reference
python3 -B frames.py
python3 -B repairs.py --sat-samples --solver cadical
```

Use `repairs.py --replay-long` to repeat both original multi-billion-state repair searches. To continue the two longer computations, take a writable copy of each saved directory. The fork includes both under `resume/`. The cumulative archive can contain a later snapshot under `search-status-136/`.

```sh
python3 -B windows.py near-nine /path/to/near-nine
python3 -B heawood.py /path/to/heawood
```

The kernel build uses Lean 4.36.0 at upstream commit `501dda8586110abcaebe0ea32060309d020bb2ee`, with Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and the corresponding Lake dependencies installed.

```sh
python3 -B proofs.py /path/to/pequalnp-proofs --build /tmp/checkpoint-136-lean --jobs 2
```

The four new Lean modules supply 13 audited declarations covering the symmetry count, the rectangle reductions and the finite-group implications. One imported module contributes five earlier audited declarations. The subgroup inventories, weighted covering decisions and local coloring exclusions are exhaustive computations. [Verification receipt](verification.json)
