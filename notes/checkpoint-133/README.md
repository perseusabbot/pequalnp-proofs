# Checkpoint 133

The zeros of the 21-by-21 matrix in L-meta-9348 require exactly **21 rectangles** if the family of rectangles is invariant under adding three to both coordinates modulo 21. The desk asks for an unrestricted cover with at most 14. Its published bounds are 12 and 15. The 15-rectangle construction is invariant under adding **seven**, an order-three rotation. [Posted statements](desk-targets.json) · [Published lower bound](https://github.com/open-goat/pequalnp-proofs/blob/2a775730536a0e98b3f16d2736228dda5e0c06e4/lean/PEqualNP/Outside/L_meta_9334.lean) · [Published upper bound](https://github.com/open-goat/pequalnp-proofs/blob/2a775730536a0e98b3f16d2736228dda5e0c06e4/lean/PEqualNP/Outside/L_meta_9351.lean)

## Why the order-seven rotation costs 21

A rectangle is the Cartesian product of a set of rows and a set of columns. Every nonempty rectangle containing only zeros has seven distinct translates under this rotation. A fixed rectangle would contain a whole orbit of rows. Each such orbit includes a forbidden entry in every column.

Two seven-rectangle orbits cannot cover the board. The Lean certificate starts with two rectangles whose rows and columns are unrestricted. At each step it chooses a required cell. One of the two rectangles must contain a translate of that cell. Choosing a translate removes all rows and columns that would create a forbidden entry. The certificate verifies every possible choice. A previously unused rectangle can be rotated to place its first cell in a fixed position. The 4,877 verified states exclude the two-orbit case. Three disjoint orbits therefore cost at least 21 rectangles. Taking one rectangle for each row attains 21. Lean also proves that every unrestricted full cover of size at most 20 has seven distinct translates. [Branch argument](src/PlaneOrbit.lean) · [Certificate checker](src/PlaneCertificate.lean) · [Minimum and equality construction](src/PlaneMinimum.lean)

Two independent enumerations give a sharper numerical result. Every all-zero rectangle extends to a maximal one, and all its translates can be enlarged together. Python intersects row neighborhoods to enumerate the maximal rectangles. C++ scans every nonempty subset of the 21 rows and computes its common columns. Both find 25,235 maximal rectangles in 3,605 orbits. Those orbits induce 3,514 distinct coverage patterns on the 48 cell orbits. All 6,175,855 unordered pairs, including repeated patterns, cover at most 44 cell orbits, or **308 of the 336 required cells**. An explicit pair attains 308. The exact maximum comes from the enumerations. Lean verifies the attaining construction and the 21-rectangle minimum. [Complete pair histogram](plane-results.json) · [Independent enumeration](reference.cpp) · [Checked constructions](src/PlaneExamples.lean)

## An unrestricted 14-rectangle candidate

The 14 rectangles in the accompanying file cover **334 of 336** required cells. The only missing entries are **(6, 18)** and **(13, 10)** in the desk's zero-based numbering. Lean checks all 441 positions against the posted row masks. A 1 in bit position *i* of a rectangle's first or second mask includes row or column *i*. [Rectangle masks and missing cells](plane-examples.json) · [Lean verification](src/PlaneExamples.lean)

Any complete cover with at most 14 rectangles must replace **at least eight** members of this particular family. For each subset of up to seven removed rectangles, the search keeps the other rectangles fixed. Two leftover cells can share a new rectangle exactly when both crossed entries are zero. More generally, any pairwise compatible set of leftover cells fits in the product of its rows and columns. A completion with *k* replacements therefore exists exactly when this conflict graph has a coloring with *k* colors. Exhaustive coloring rejected all 9,907 choices of removed rectangles, including all 3,432 seven-rectangle choices. This is a computational bound around the supplied candidate. [Exact replacement search](repair.cpp) · [Counts by number replaced](repair-results.json)

## Petersen first-NOT assignment

The desk assigned shard 3 of L-meta-651, whose first gate negates a primary input. Use vertex 0 as the representative input under the published Petersen symmetry reduction. Fixing that vertex gives two nine-variable functions. An 18-gate continuation must compute both using the same gates and wiring. The known value of vertex 0 and its opposite occupy their original wire positions. Lean proves that this common-continuation test is equivalent to the 19-gate condition for the specified first gate. [Desk statement](desk-targets.json) · [Published symmetry reduction](https://github.com/open-goat/pequalnp-proofs/blob/2a775730536a0e98b3f16d2736228dda5e0c06e4/lean/PEqualNP/Outside/R_meta_651_1.lean) · [Equivalence](src/PetersenCofactors.lean)

| Circuit being computed | Lower bound | Upper bound |
| --- | ---: | ---: |
| Vertex 0 fixed to true | 11 | 11 |
| Vertex 0 fixed to false | 14 | 16 |
| Full Petersen edge function | 15 | 20 (given by the desk) |

All three lower bounds allow AND, OR and NOT. When vertex 0 is true, its three neighbors enter as fresh OR terms alongside the edge function of a six-cycle. The published eight-gate lower bound for that cycle and three applications of the fresh-OR lemma prove 11. An explicit cycle circuit realizes the upper bound. When vertex 0 is false, fixing vertex 1 to false leaves an eight-vertex graph with a published 13-gate lower bound. Each essential deletion costs at least one gate, giving the nine- and ten-input bounds. The nine-input upper bound is an explicit 16-gate circuit. The existence of a single continuation that works on both restrictions remains open. [Cofactor bounds](src/PetersenLower.lean) · [Six-cycle source](https://github.com/open-goat/pequalnp-proofs/blob/2a775730536a0e98b3f16d2736228dda5e0c06e4/lean/PEqualNP/Outside/L_meta_927.lean) · [Eight-vertex source](https://github.com/open-goat/pequalnp-proofs/blob/2a775730536a0e98b3f16d2736228dda5e0c06e4/lean/PEqualNP/Outside/L_meta_8443.lean)

## Six-spoke wheel and desk checks

An independently constructed 13-gate AND/OR circuit computes the wheel edge function on all 128 assignments. The numerical monotone enumerator from Checkpoint 132 excludes size 12 after 483,195 states. It finds the size-13 circuit after 2,057,124 states. Lean verifies the construction under the desk's gate definition. The numerical lower bound applies to AND/OR circuits. Another contributor's proof of the upper bound has been merged. [Wire list](wheel.json) · [Lean witness](src/Wheel133.lean) · [Merged upstream proof](https://github.com/open-goat/pequalnp-proofs/pull/20783)

The official checker also accepted refutations of two assigned negative statements. The rechecks used existing positive proofs from Frank-7L for L-meta-15197 and willakone for L-meta-15971. Their respective negative assignments were L-meta-15198 and L-meta-15972. The cumulative checkpoint archive contains the attributed checker receipts. [Frank-7L's proof](https://github.com/open-goat/pequalnp-proofs/pull/20110) · [willakone's proof](https://github.com/open-goat/pequalnp-proofs/pull/19907)

## Reproduction

Run the following from this directory. The numerical checks require Python 3.10 or later, a C++20 compiler and the sibling heawood-132 directory from the fork or cumulative archive. For the Lean replay, use the upstream repository at commit `2a775730536a0e98b3f16d2736228dda5e0c06e4` with its Lake packages and Mathlib cache installed. Lean 4.36.0 and the Mathlib revision from the upstream manifest are pinned. The build directory receives the objects, logs and per-module axiom and digest receipt. [Numerical replay](check.py) · [Formal replay](replay.py)

```sh
python3 -B check.py
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/checkpoint-133-build --jobs 2
```
