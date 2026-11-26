# Checkpoint 135 · Symmetries of small rectangle covers

Every complete cover of the 21 × 21 board using at most 14 rectangles has a number of distinct images divisible by **15,120** under the generated group of 241,920 board symmetries. For a cover of size 15, the divisor is **5,040**. In particular, at most 16 of the 241,920 maps can fix a cover of size at most 14. The proof combines exact minima for the remaining order-three symmetries with an exhaustive search over subgroups of an explicit 128-element group.

The minimum is **16 rectangles** for each of the two remaining kinds of order-three symmetry. Both attaining covers are included.

The unrestricted minimum remains between 13 and 15. Jonathan Chassot (`JLDC`) proved the lower bound of 13, and `DPS0340` constructed a cover of size 15. [Lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [Upper bound](https://github.com/open-goat/pequalnp-proofs/pull/13338)

## Which symmetries cost an extra rectangle?

A rectangle is a product of a row set and a column set containing only zeros. A family is invariant if the symmetry permutes its distinct rectangles. Every subgroup of a given class in this table is conjugate to the representative used in the computation. Conjugation transports both covers and lower bounds.

| Order | Geometry of the representative | Number of subgroups | Minimum for an invariant cover |
| --- | --- | ---: | ---: |
| 3 | Simultaneous translation by seven, no fixed rows | 960 | 15 |
| 3 | Three fixed rows and three fixed columns | 1,120 | **16** |
| 3 | Six fixed rows and six fixed columns | 336 | **16** |
| 5 | One fixed row and one fixed column | 2,016 | 16 |
| 7 | Simultaneous translation by three, no fixed rows | 960 | 21 |

The three-row and six-row cases are called `triangle3` and `homology3` in the files. The three order-three classes account for all 4,832 elements of order three. The size-16 witness for the three-row case itself has nine stabilizing symmetries, eight of order three. The six-row witness has three stabilizing symmetries. [Coordinate maps and witnesses](actions.json) · [Previous order-three and order-five results](../checkpoint-134/README.md) · [Order-seven result](../checkpoint-133/README.md)

## Exhausting the cases through 15

An invariant family consists of fixed rectangles and triples. Delete duplicates and rectangles that cover no cells. Extend each remaining rectangle by taking all columns common to its rows and then all rows containing those columns. This construction commutes with the two axis permutations. If extensions coincide, keep one copy. It suffices to test families of the 25,235 nonempty maximal legal rectangles.

| Quotient data | Three fixed rows | Six fixed rows |
| --- | ---: | ---: |
| Cell orbits | 114 | 126 |
| Fixed maximal rectangles | 62 | 197 |
| Moving triples of maximal rectangles | 8,391 | 8,346 |
| Cell orbits outside all fixed rectangles | 45 | 40 |
| Fixed triples before symmetry reduction | 37,820 | 1,254,890 |
| Fixed triple representatives | 1,480 | 9,623 |
| First moving representatives in the five-triple search | 123 | 9 |

- **At most three moving triples.** Three cannot cover the cells outside all fixed rectangles, even with arbitrarily many fixed rectangles. A Lean certificate chooses one representative of each such cell orbit. Assigning it to a moving rectangle requires choosing a rectangle and one of three phases. Whenever two choices use the same rectangle, both crossed entries have to be zeros. The checked search exhausts those choices. A separate enumeration reaches the same conclusion on the maximal rectangles.
- **Four moving triples.** There is room for at most three fixed rectangles. Test the residual for each possible fixed triple, up to the normalizer of the rotation. Padding to three distinct fixed rectangles can only help. A second search starts from the moving rectangles instead. It enumerates four moving triples covering the cells outside all fixed rectangles, then tries to cover their residual with three fixed rectangles.
- **Five moving triples.** All 15 slots are occupied. At least one of the five triples must cover a fifth or more of the cell orbits. Enumerate every symmetry class of such a first triple, then test whether four more can cover the residual. A separate Python implementation intersects cell postings to repeat the test.

The fixed-triple reduction uses a normalizer of order 216 for the three-row case and 720 for the six-row case. The checker constructs their permutations of the fixed rectangles and verifies that the classes partition every fixed triple. The corresponding first-moving reductions also check their full partitions. [Enumeration](search.py) · [Four-orbit residual search](four.cpp) · [Independent search starting at the boundary](boundary.cpp)

Lean checks both 16-rectangle upper bounds on the original 441 entries, the board symmetries, and the entire branch with at most three moving triples. The four- and five-triple exclusions are exhaustive computational results. The same Lean checker proves that two moving groups cannot cover the 46-cell boundary in the order-five case from Checkpoint 134. [Board witnesses](src/Witnesses.lean) · [Soundness of the finite search](src/OrbitSearch.lean) · [Connection to legal rectangles](src/OrbitGeometry.lean)

## Why the orbit divisors increase

The generated group has order `2^8 × 3^3 × 5 × 7`. For a cover of size at most 14, no element of order three, five, or seven fixes the family. Cauchy's theorem makes its stabilizer a 2-group. Orbit–stabilizer then supplies the full odd divisor, `3^3 × 5 × 7 = 945`.

At size 15, an element of order three in the stabilizer can only belong to the class that fixes no row or column. Consider the stabilizer acting on all 42 row and column labels. The subgroup fixing a label has order coprime to three. If nine divided the order of the family stabilizer, each orbit of labels would have size divisible by nine. Their sizes sum to 42. Thus the stabilizer has at most one factor of three. The order-five and order-seven exclusions still apply, giving `3^2 × 5 × 7 = 315`. Lean proves both group-action implications from their prime-order hypotheses. Enumeration of the board group and the symmetry exclusions establish those hypotheses. [Group-action proof](src/OrbitDivisibility.lean)

## A factor of 16 from a group of order 128

Three explicit axis-preserving generators in `actions.json` generate a group of order 128. Its subgroups of order at least 16 cannot stabilize any complete cover of size at most 15.

| Subgroup order | All subgroups | Classes under conjugation by the group of order 128 | Subgroups admitting a cover of size at most 15 |
| ---: | ---: | ---: | ---: |
| 128 | 1 | 1 | 0 |
| 64 | 7 | 7 | 0 |
| 32 | 31 | 19 | 0 |
| 16 | 79 | 35 | 0 |

The checker descends through index-two kernels. It independently generates every subgroup of order at most 16 by adjoining elements, then compares the complete lists at order 16. Every subgroup of larger order in a finite 2-group contains one of order 16. For a given subgroup, rectangular extension commutes with its permutations of the two axes. A maximal-rectangle orbit costs its number of rectangles and covers a set of cell orbits. The exact cost search selects an uncovered cell and tries every affordable rectangle orbit that meets it. A bound on how many remaining cells can be covered at each cost shortens the search. The full replay tests all **118 subgroups** individually.

Act with this 128-element group on the images of any complete cover of size at most 15. Every stabilizer in this action has order dividing eight. Consequently each orbit has size divisible by 16, and their disjoint union does too. Combining 16 with the odd divisors 945 and 315 gives **15,120** for at most 14 rectangles and **5,040** for size 15. The verified group-action lemma also applies to an orbit collection with more than one component under the subgroup. [Subgroup enumeration](two_groups.py) · [Exact weighted cover search](budget.cpp) · [Group-action proof](src/OrbitDivisibility.lean)

## Improving the 334-cell example

The Checkpoint 133 family of 14 rectangles misses exactly two zeros, `(6,18)` and `(13,10)`. A symmetry that exchanges the row and column sides interchanges these holes. It fixes four of the rectangles and pairs the other ten. Lean checks this description on the original board.

A complete coloring search tested all 3,432 ways of keeping seven of the rectangles. **Every such 14-rectangle family covers at most 334 zeros**, even when the search may choose its one omitted zero anywhere. It visited 233,013,747 states. Applying the board group gives **411,324,480 distinct sets of seven rectangles** excluded as subsets of any family of at most 14 rectangles that covers 335 or more zeros. The 3,432 original sets occupy 1,741 orbits. Two counts, one by stabilizers and one by returns to the original family, give the same total.

If the one permitted omission is one of the two original holes, a family retaining six original rectangles also falls short of 335 covered zeros. All 3,003 choices failed in 350,375,076 states. The symmetry exchanging the holes gives the other orientation. The coloring graph always uses the full board to test the two crossed entries, including the permitted omission. This preserves the requirement that every rectangle be legal. The bounds around this example are computational. [Coloring search](nearcover.cpp) · [Subset and duality checks](local.py)

## Symmetries that exchange the two axes

The group has 1,288 involutions that exchange rows and columns. Identify each row with its partner column. The symmetry becomes transposition, and a cell orbit becomes an unordered pair. A fixed rectangle is a square on a set of vertices. If a diagonal entry is forbidden, no fixed square can touch that vertex. Every allowed pair with both diagonal entries allowed lies in the fixed square on its two ends.

For the 1,008 involutions with five forbidden diagonal entries, exactly **four moving pairs** suffice to cover all 70 unordered cells beyond the reach of fixed squares. Three pairs fail. The symmetry of the 334-cell example belongs to this class. For the other 280 involutions, nine diagonal entries are forbidden and the boundary has 108 cells. Exactly **seven moving pairs** are needed. Five fail in all 19 first-pair classes. For six pairs, normalize a largest first pair and then a pair with largest remaining coverage. This leaves 36 possible first-pair classes and 14,777 distinct unions of the first two pairs. Four more pairs fail on every residual. An explicit seven-pair family covers the boundary. A complete invariant family with at most 14 rectangles must therefore consist of precisely seven exchanged pairs. The boundary witnesses in this paragraph allow additional fixed squares to cover the rest of the board.

A cover of size at most 13 and each of its group images avoid all 280 of the nine-diagonal involutions. Any one of these involutions partitions the images into disjoint pairs. The number of images is therefore even as well as divisible by 945, giving an independent divisor of **1,890**. [Exhaustive boundary checks](dualities.py) · [Paired rectangles](actions.json)

## Replay

From this directory, Python 3.10 or later and a C++20 compiler reproduce the numerical results.

```sh
python3 -B search.py --independent --jobs 2
python3 -B two_groups.py --all-subgroups
python3 -B local.py --solve both
python3 -B dualities.py
python3 -B build_certificates.py
```

These commands repeat the order-three searches in both directions, test all 118 subgroups of orders 16 through 128, rebuild the one-hole instances from the published family, and check the two classes of side-swapping involutions. The final command regenerates the three finite proof certificates in memory and compares them byte for byte with the Lean sources.

For the kernel replay, use Lean 4.36.0 with upstream commit `501dda8586110abcaebe0ea32060309d020bb2ee` and its Lake dependencies and Mathlib cache installed.

```sh
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/checkpoint-135-build --jobs 1
```

The replay builds the upstream board definitions and all local modules. It checks the final axiom lists against `propext`, `Classical.choice` and `Quot.sound`. [Results](results.json) · [Verification receipt](verification.json)
