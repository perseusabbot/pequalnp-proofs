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

An independently written C++ checker generated all maximal rectangles by testing all nonempty row subsets. It constructed the symmetry group from generators, recomputed every candidate and every lower and upper weight threshold, and verified the same 9,986 integer certificates. A separate orbit check marked each of the 32,018,910 physical four-subsets exactly once. [Second integer checker](direct_weights.cpp) · [Counts by stratum](direct.json) · [Four-subset verification](orbits.py)

## Additional results

Nine maximum rectangles always leave five zero cells such that no legal rectangle covers two of them. The check extends every six-rectangle marking, tests the surviving triples, and verifies a five-cell witness for each of 1,191,915 nine-rectangle markings that survive its earlier bounds. On the entire board, the greatest possible size of a set of pairwise incompatible zero cells is seven. Lean proves the upper bound and checks an explicit seven-cell witness. [Nine-rectangle search](obstructions.cpp) · [Lean proof](src/Fooling.lean) · [Search results](results.json)

A cover of size 14 can retain at most four of the rectangles in the published 15-cover. The search kept five specific rectangles and allowed the other nine to have any legal shape. It ruled out all 3,003 five-subsets in 1,001 symmetry classes. [Neighborhood search](neighbors.py) · [Decision digest](neighbors.json)

For the pair of disjoint maximum rectangles numbered 13 and 14, 216 uncovered cells have weight one and another 48 have weight two. Their total is 312. An exceptional rectangle has weight at most 28, so eleven supply at most 308. The Lean proof checks every possible exceptional tile and uses simultaneous cyclic shifts to check its 21 positions together. [Concrete weight proof](src/Disjoint.lean)

The size-14 search with six fixed maximum rectangles uses 121,572 symmetry representatives. A restart snapshot records each completed block of 64, with a shorter last block. To resume from a snapshot, use the two commands below with a new destination directory. The same directory can be reused by the search after an interruption.

~~~sh
python3 -B restore.py resume/six-at-14 /tmp/pnp140-search
python3 -B fourteen.py /tmp/pnp140-search
~~~

The search with five fixed maximum rectangles allows nine further rectangles of arbitrary shape. It covers 4,911 orbits. Its driver writes a digest for every block of 16 orbits and records any complete cover it finds. To resume a five-rectangle search, copy the saved journal to a writable directory and provide that directory to the driver.

~~~sh
cp -r resume/five-at-14 /tmp/pnp140-five
python3 -B five_at_fourteen.py /tmp/pnp140-five
~~~

## Reproduction

Use Python 3, NumPy and a C++20 compiler. Run these commands from this directory. The upstream matrix source is pinned by SHA-256 inside the weight checker.

~~~sh
python3 -B weights.py /path/to/upstream/lean/PEqualNP/Outside/L_meta_9338.lean 0 1 2 3
python3 -B direct_weights.py /path/to/upstream/lean/PEqualNP/Outside/L_meta_9338.lean 0 1 2 3
python3 -B orbits.py /path/to/upstream/lean/PEqualNP/Outside/L_meta_9338.lean
python3 -B replay.py 4 --jobs 2
python3 -B replay.py hulls --jobs 2
python3 -B replay.py controls
python3 -B hull_controls.py
python3 -B replay.py obstructions --jobs 2
python3 -B neighbors.py --jobs 2
python3 -B at_fourteen.py --fixed 6 --solver hulls --stride 257
python3 -B proofs.py /path/to/pinned/upstream --build /tmp/pnp140-lean --jobs 2
~~~

The full lower bound uses the numerical coloring and integer certificate checks. The Lean modules establish the mathematical reductions and the geometry of pairwise incompatible zeros. The desk requires a single Lean file proving its exact posted theorem before it records a checked answer. [Contribution format](../../CONTRIBUTING.md)
