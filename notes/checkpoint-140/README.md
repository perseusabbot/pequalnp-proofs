# Checkpoint 140

**Covering all 336 zeros of the desk’s 21 by 21 matrix takes at least 14 all-zero rectangles.** The published 15-rectangle cover gives an upper bound of 15. An exhaustive computation establishes the new lower bound. The desk’s lower-bound question at size 13 is L-meta-9345. [Desk record](desk.json) · [Published 15-cover](https://github.com/open-goat/pequalnp-proofs/pull/13338)

Every rectangle can be enlarged to an inclusion-maximal legal rectangle. The board has 168 legal 6 by 6 rectangles and 25,067 other nonempty maximal rectangles. Call the first group maximum rectangles. A proposed cover of size at most 13 either contains at least four distinct maximum rectangles after enlargement, or it contains zero, one, two or three. Duplicates can be discarded.

## Four fixed maximum rectangles

There are 32,018,910 unordered selections of four maximum rectangles. They split into 235 orbits under board symmetries. Fix a representative and remove the cells it covers. Two remaining zeros conflict if a crossed entry is one. Covering the residual by nine legal rectangles is equivalent to coloring its conflict graph with nine colors. Each legal rectangle covers an independent set. Conversely, the row-by-column product of an independent set is legal. Lean proves the equivalence on the posted board. [Coloring equivalence](src/ColorCover.lean)

Two programs independently excluded all 235 cases. The first assigned colors to residual cells and visited 176,880,656 search states. The second reconstructed the maximum rectangles from all six-row choices, grew rectangles directly, and removed every cell covered by each growing row-by-column product. It visited 165,751,473 states. The other nine rectangles in these searches could have any legal shape. [Color search](coloring.hpp) · [Independent rectangle search](hulls.cpp) · [Orbit construction](anchors.cpp)

## Zero through three maximum rectangles

Fix the maximum rectangles in a prospective cover. The remaining rectangles must come from the other 25,067 maximal choices. An integer certificate gives a nonnegative weight to each uncovered zero. If their total weight exceeds the remaining budget times the greatest weight of any eligible rectangle, the proposed cover is impossible.

When this inequality does not yet exclude a cover, choose its heaviest remaining rectangle. Its weight is at least the total uncovered weight divided by the remaining budget. After choosing it, every other member weighs at most as much. Each must also cover enough of the newly exposed weight for the other slots to supply the balance. The checker enumerates every eligible heaviest choice up to symmetries fixing the marked rectangles. It verifies that all weights used for an orbit split are invariant under those symmetries. [Weight inequalities in Lean](src/Weights.lean) · [Integer checker](weights.py)

| Fixed maximum rectangles | Physical fixed families | Symmetry representatives | Integer weight certificates |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 8,492 |
| 1 | 168 | 1 | 1,170 |
| 2 | 14,028 | 4 | 150 |
| 3 | 776,216 | 20 | 174 |

The four rows contain 9,986 certificates. The longest path chooses three exceptional rectangles. The checker reads the upstream matrix, rebuilds all maximal rectangles, and performs every exclusion with integer arithmetic. Its decision uses only the published weights, the allowed rectangles and the board symmetries. [Certificates](certificates) · [Weight receipts](weights.json)

## Reproduction

Use Python 3, NumPy and a C++20 compiler. Run these commands from this directory. The upstream matrix source is pinned by SHA-256 inside the weight checker.

~~~sh
python3 -B weights.py /path/to/upstream/lean/PEqualNP/Outside/L_meta_9338.lean 0 1 2 3
python3 -B replay.py 4 --jobs 2
python3 -B replay.py hulls --jobs 2
python3 -B replay.py controls
python3 -B replay.py obstructions --jobs 2
python3 -B proofs.py /path/to/pinned/upstream --build /tmp/pnp140-lean --jobs 2
~~~

The full lower bound uses the numerical coloring and integer certificate checks. The Lean modules establish the mathematical reductions and the geometry of pairwise incompatible zeros. The desk requires a single Lean file proving its exact posted theorem before it records a checked answer. [Contribution format](../../CONTRIBUTING.md)
