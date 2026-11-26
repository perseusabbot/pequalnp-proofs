# Checkpoint 134 · Rotation symmetry on the 21 × 21 rectangle board

**The minimum is 15 when the family is invariant under adding seven to both coordinates modulo 21.** The published cover of size 15 has this symmetry. Combined with Checkpoint 133, this proves that every cover of size at most 14 has 21 distinct simultaneous translates. The unrestricted minimum lies between 13 and 15. The desk still lists the existence questions at 13 and 14 as open.

Jonathan Chassot (`JLDC`) proved the new unrestricted lower bound of 13. The order-three proof here uses his verified list of containing rectangles. `DPS0340` supplied the published upper bound. [Unrestricted lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [15-rectangle construction](https://github.com/open-goat/pequalnp-proofs/pull/13338)

## Why the rotation forces 15

There are 336 zeros. Simultaneous translation by seven partitions them into 112 orbits. A family of distinct rectangles closed under this translation consists of fixed rectangles and groups of three. Repeated list entries can be removed before taking the partition. Every nonempty legal rectangle can be extended by taking all columns common to its rows and then all rows common to those columns. This extension commutes with the rotation. The board has 25,235 maximal rectangles, of which 14 are fixed. The others form 8,407 groups of three.

| Moving groups | Fixed rectangles allowed in the lower-bound test | Reason a cover fails |
| --- | --- | --- |
| At most 2 | All 14 maximal fixed rectangles | There are 49 cell orbits outside their union. A moving group reaches at most 17. |
| 3 | At most 5 | Exactly 14 triples reach all 49 outside orbits. Each needs at least seven fixed rectangles to finish. |
| 4 | At most 2 | The 91 distinct fixed pairs fall into four symmetry classes of sizes 42, 21, 21 and 7. All four residuals fail. |

A family with five moving groups already has 15 rectangles. For the four-group row, 84 explicit coordinate maps preserve the board, conjugate translation by seven to itself or its inverse, and reduce the pair choices to four representatives. Repetition and unused slots are permitted in the lower-bound proof. A separate exhaustive search checks the four residuals by intersection of cell postings and remaining-area bounds. Running the direct search on every one of the 91 fixed pairs also excludes them all without using the symmetry classification.

The finite certificates use nonnegative integer weights on cells. At each step, every surviving candidate has score at most the stated cap. A candidate can be removed if its score plus the maximum contribution from all other slots is below the total cell weight. The earliest removal among the members of a hypothetical cover gives a contradiction. Two slot types have separate caps. The four residual certificates use 247, 194, 198 and 110 weight tests. The two mixed cases use one and 26 tests. All 776 tests use integer arithmetic.

The Lean proof treats all legal rectangles. It projects the containing rectangles from the upstream proof to 8,435 indexed masks, including dominated or empty cases. It checks the weights, scores and eliminations for those masks, proves the symmetry reductions, and verifies the attaining cover on the board. The public list formulation includes repeated entries. The full translation result uses the order-seven lower bound from Checkpoint 133. [Exact minimum](src/Minimum.lean) · [All 21 translates](src/AllTranslations.lean)

## Unrestricted covers near the 14-rectangle example

The example in Checkpoint 133 covers 334 zeros, missing only `(6,18)` and `(13,10)` in zero-based coordinates. Exhaustive coloring tried all 3,003 ways to keep six of its rectangles and replace the other eight. All failed. The search visited 337,987,474 states, with 1,939,485 in the largest case. A complete cover of size at most 14 must replace at least nine members of this example.

Four explicit board symmetries generate 241,920 maps and 120,960 distinct images of the example. Its 3,003 six-rectangle subsets occupy 1,500 orbits. Of those orbits, 1,423 have stabilizer size 1, 73 have size 2, two have size 4 and two have size 6. Their sizes sum to **353,283,840 distinct six-rectangle sets** that cannot be contained in a complete cover of size at most 14. A separate count by the number of group elements returning each subset to the original example gives the same total. The local coloring exclusion and the orbit count are computational results. [Incumbent and missing cells](../checkpoint-133/plane-examples.json) · [Group enumeration](anchors.py)

## An order-five symmetry

For the row and column permutations in `board.json`, the invariant minimum is **16**. Of 68 cell orbits, 46 lie outside all five fixed maximal rectangles. Two moving groups can cover at most 41 of these 46, even with all five fixed rectangles available. Exhaustive search also excludes three moving groups without a fixed rectangle. One fixed rectangle and three five-element groups do cover the board. The lower bound has a standalone computational replay. Lean checks the symmetry's order, its preservation of the board and the explicit 16-rectangle witness. [Symmetry and witness](src/OrderFive.lean)

## A larger orbit for every prospective cover

Under the 241,920 generated board symmetries, the number of distinct images of any complete cover of size at most 14 is **a multiple of 105**. The generated group has order `2^8 × 3^3 × 5 × 7`. Conjugating the three excluded cyclic symmetries gives 960 subgroups of order three, 2,016 of order five, and 960 of order seven. Enumeration also counts every group element of orders five and seven and verifies that those two lists of subgroups are exhaustive.

Take all images of a putative cover under the generated group. Each image is again a cover of size at most 14. The simultaneous translations partition these images into sets of 21 by the Lean theorem. The order-five permutation also partitions them into sets of five, since an orbit of size one would give an invariant cover smaller than 16. The number of images is therefore divisible by both 21 and 5. This deduction uses the computational order-five exclusion alongside the Lean translation theorem. [Group computation](anchors.py)

## Replay

From this directory, run the following with Python 3.10 or later. The numerical scripts use the standard library.

```sh
python3 -B verify.py --direct
python3 -B anchors.py
python3 -B radius.py --solve
```

Use `python3 -B verify.py --all-pairs --jobs 2` for the longer direct check of all 91 fixed pairs in Python and an independent C++20 implementation. The last command in the block compiles the C++20 search from Checkpoint 133, reconstructs the input from its published witness, and checks the full eight-replacement result. The nine-replacement input is reproducible with `python3 -B radius.py --radius 9 --write-input nine.in`. The numerical outputs for this checkpoint are in `results.json`.

For the kernel replay, use Lean 4.36.0 and an upstream checkout at commit `501dda8586110abcaebe0ea32060309d020bb2ee` with its Lake dependencies and Mathlib cache installed. Run the following from the fork's checkpoint directory.

```sh
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/checkpoint-134-build --jobs 2
```

The script builds both upstream rectangle proofs, rebuilds the local proof and the Checkpoint 133 geometry imports, and audits the final declarations against the standard Lean axioms. It writes per-module logs and a JSON receipt in the build directory. [Pinned upstream source](https://github.com/open-goat/pequalnp-proofs/tree/501dda8586110abcaebe0ea32060309d020bb2ee/lean/PEqualNP/Outside)
