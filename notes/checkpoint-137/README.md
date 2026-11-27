# Checkpoint 137

The 21 by 21 matrix has 336 zero entries. An all-zero rectangle is the product of any set of row labels and any set of column labels whose intersections are all zero. The unrestricted minimum is between 13 and 15 inclusive. Jonathan Chassot proved the lower bound of 13. DPS0340 exhibited a cover of size 15. The desk snapshot of November 27 still lists both the existence and the impossibility questions at sizes 13 and 14. [Lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [Upper bound](https://github.com/open-goat/pequalnp-proofs/pull/13338) · [Desk snapshot](desk.json)

**Exactly 16 rectangles are necessary and sufficient when every rectangle must fit inside a legal 6 by 6 rectangle.** Each such rectangle can be enlarged to 6 by 6. An exhaustive search rules out 15, and an explicit family of 16 covers the board. There is also a 15-member family of 6 by 6 rectangles that misses just two cells. With labels starting at zero, they are row 8, column 16 and row 10, column 16. [Witness masks](witnesses.json) · [Lean certificate](src/MaximumRectangles.lean)

**Every cover of size at most 14 requires at least two rectangles that cannot fit inside any legal 6 by 6 rectangle.** All row and column labels were available. At size 13, at least **three** rectangles must each fail to fit inside any legal 6 by 6 rectangle. These statements apply to families with arbitrary symmetry.

## Geometry and the seven cases at size 15

Enumerating all choices of six rows and their common zero columns gives 168 distinct 6 by 6 rectangles. An independent computation closes arbitrary row sets under their common columns and gives 25,235 nonempty maximal rectangles. The two inventories agree on the 168 rectangles of area 36. Every other maximal rectangle has area at most 28.

Every row and column has 16 zeros and lies in 48 of the maximum rectangles. Each zero lies in 18 maximum rectangles. For two distinct maximum rectangles, the number of shared rows equals the number of shared columns. Fixing one rectangle, exactly 10 others share zero rows with it, 72 share one, 45 share two, and 40 share three. A triple through a given row can cover all 16 of its zeros in 96 ways. Each such triple meets in one common column and covers all sixteen zeros of that column as well. Lean proves this for every triple on the posted board. Checking the local unions shows that a triple that falls short covers at most 14 zeros in that row.

In a complete cover by these rectangles, each row and column must belong to at least three. If a label belongs to exactly three, a board symmetry takes it to row zero. The stabilizer of that row takes any of its 96 covering triples to the same representative. Otherwise every label belongs to at least four rectangles. Fifteen rectangles supply only 90 row memberships, so some row belongs to exactly four. The 7,320 covering quadruples through that row split into six orbits under its stabilizer. The search excludes the triple case and all six quadruple cases at budget 15. Symmetry only identifies different names for the same case. The chosen cover itself can have a trivial stabilizer. [Orbit sizes and decisions](results.json)

## Allowing an arbitrary rectangle

If every box except one fits into a legal 6 by 6, enlarge those boxes. Extend the exceptional box to a maximal legal rectangle. Repeated extensions may be deduplicated. There are eight possible shapes for an exceptional maximal rectangle, up to board symmetry and interchange of the axes. Fixing one such rectangle leaves room for 13 maximum rectangles in a cover of size 14.

A label outside the fixed rectangle still needs all 16 of its zeros covered by maximum rectangles. Either some such label belongs to exactly three of them or all such labels belong to at least four. In the first case the stabilizer of the exceptional rectangle acts on the label and its covering triple together. One representative of each orbit suffices. In the second case the search enforces the degree lower bound at every untouched label. The representative counts include that last case.

| Shape up to interchange | Maximal rectangles | Search cases |
| --- | ---: | ---: |
| 16 by 1 | 42 | 4 |
| 12 by 2 | 420 | 11 |
| 9 by 3 | 2,240 | 31 |
| 7 by 4 | 5,040 | 70 |
| 8 by 3 | 420 | 12 |
| 6 by 4 | 6,720 | 93 |
| 5 by 5 | 10,080 | 131 |
| 4 by 4 | 105 | 5 |
| **Total** | **25,067** | **357** |

## How the decisions are checked

At every label, a table indexed by the 16 local zeros gives the minimum number of additional 6 by 6 rectangles needed to cover any remaining subset there. It can underestimate the global requirement because another label may force incompatible choices. The two sums of label requirements must each fit within six memberships per chosen rectangle. If a label must finish at degree three, the search also checks whether one of its 96 covering triples is still available.

An uncovered cell must lie in some remaining rectangle. Branching on the first selected candidate for that cell partitions the possible completions. A cell with just one remaining candidate forces that rectangle. Separate positive controls recover a full cover from 15 of its 16 members and accept the supplied 16-member family. [Decision algorithm](hexads.cpp) · [Replay driver](replay.py)

As an independent check, a direct Boolean formula covers each zero and enforces degree four on every label. At budget 14 this is precisely the case in which no label has degree three. CaDiCaL finds contradictions for all six quadruple representatives. A separate checker verifies each learned clause by reverse unit propagation from the original clauses, through to the empty clause. [SAT encoding and proof checker](sat.py) · [Formula digests](sat-results.json)

Lean checks the explicit 16-rectangle witness on the original board, the incidence count, the local degree lower bound, the degree-three or degree-four split, the equality case at size 14, equality of the row and column overlaps for every pair of maximum rectangles, the common-point calculation for three six-element sets, and the lifting of arbitrary subrectangles to allowed extensions. The exhaustive search exclusions and orbit inventories use the numerical programs. The files under `certificates/` contain the six additional LRAT contradictions and can be checked directly with Python. [Axiom and computation receipts](verification.json)

## Reproduction

Run these commands from this directory in a checkout containing the preceding checkpoints. The numerical replay requires Python 3 and a C++20 compiler. The SAT replay uses a CaDiCaL build with LRAT output. The Lean command expects upstream commit `501dda8586110abcaebe0ea32060309d020bb2ee`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and Lean 4.36.0. It also compares all 441 board entries, the 168 rectangle masks and the sixteen witness IDs with the pinned source.

```sh
python3 -B replay.py --jobs 2
python3 -B sat.py --verify-traces certificates
python3 -B sat.py --solver cadical
python3 -B proofs.py /path/to/upstream --build /tmp/checkpoint-137-lean
```

## Checking two exceptional rectangles at size 13

Allowing two exceptional maximal rectangles leaves room for eleven 6 by 6 rectangles. Choose a representative of the first shape, then use its stabilizer to enumerate every possible position of the second rectangle. Different shapes are ordered by their shape index. For equal shapes both orientations are allowed, so some unordered pairs occur twice. This convention gives 2,487 cases and accounts for 402,926,972 pairs with the stated orientation convention. The solver begins with the union of the two exceptional rectangles already covered. All 2,487 cases at total size 13 were excluded in 205,143,184 states. A pair of identical maximal extensions reduces to the single-exception case. This exhausts all 314,164,711 unordered choices of two distinct exceptional maximal rectangles. The search at size 14 with two exceptions is still in progress. [Pair search](pairs.py) · [Saved decisions](resume/two-other/decisions.json)

To restart a saved search, copy its directory under `resume/` to a writable location and run the corresponding command. The pair journal stores a consecutive prefix of the deterministic case order. Its signature binds the board, rectangle order, pair inventory, budget and solver source. Starting in an empty directory replays all pair cases from scratch. The other journals preserve the size-14 pair search, the unrestricted one-hole search and the reduced Heawood circuit search.

```sh
python3 -B pairs.py /path/to/two-other --total 13
python3 -B pairs.py /path/to/two-other-14 --total 14
python3 -B ../checkpoint-136/windows.py near-nine /path/to/near-nine
python3 -B ../checkpoint-136/heawood.py /path/to/heawood
```
