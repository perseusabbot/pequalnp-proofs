# Eight lost edge inputs in a 26-gate Heawood circuit

The Heawood edge function takes 14 input bits, one per vertex. It is true when both ends of at least one of the 21 edges are selected. In any correct circuit of at most 26 two-input AND and OR gates, forcing every nested AND output to zero makes **at least eight** of the 21 individual edge inputs false. An AND is nested when either operand depends on an earlier AND. Checkpoint 124 gave a lower bound of six.

| Gate limit | Minimum edge inputs lost |
| ---: | ---: |
| 26 | 8 |
| 25 | 9 |
| 24 | 10 |
| 23 | 12 |
| 22 | 12 |
| 21 | 14 |

The proof allows wire sharing, repeated operands, arbitrary output wires and the evaluator's default zero for unavailable operands. It also applies to all 65 prescribed opening pairs and all four choices of their operations in the project's packed search, L-meta-3541 under L-meta-3004. The existence of a correct 26-gate circuit remains open. [Posted statement](statement.txt)

## A gate bound from the missing edges

Write H for the surviving edges, L for the missing edges, D for the vertices incident to L, and j for the number of distinct ordinary AND products represented at the pruned output. If the original circuit has g gates, then

`|H| + |D| + j ≤ g + 1`.

If L contains a path of three consecutive edges on four distinct vertices, then

`|H| + |D| + j ≤ g`.

To see why each vertex in D costs a separate input to the remaining computation, take a missing edge xy. Compare the positive input selecting x and y with the input selecting y and every nonneighbor of y on x's side of the bipartition. The latter input contains no edge. A regular signal can distinguish these two inputs only if it is the singleton x. Here a regular signal is the OR of at most one input or the OR of some neighbors of a single vertex in H. The absence of a four-cycle gives the singleton conclusion. Reversing x and y forces the other endpoint as well.

On inputs where all retained products are false, replace each retained product by its own zero-valued leaf and each regular AND-free wire by its signal. The contracted circuit uses at most g − |H| binary gates. All j product labels and all |D| distinct singleton labels must occur. A circuit of k binary gates has at most k + 1 distinct input labels in a single output. At equality, expanding the output gives a formula in which each leaf occurs once.

On a missing path a–b–c–d, turn off every off-path vertex. Setting a and d both to zero leaves b AND c. Setting both to one gives b OR c. The four vertices span exactly the three path edges, so the retained products vanish under both settings. A monotone formula with one occurrence of each of b and c cannot switch between those two functions. Lean checks the two-variable truth tables and proves the rule by induction on the formula. This rules out equality in the first bound whenever a path is present.

## Finite counts

The surviving edges have a vertex cover of size at most j. Any matching in H therefore gives a lower bound on j, as does rounding |H| / 3 up. When 4|L| > 3|D|, L must contain a three-edge path. In the absence of such a path, every missing edge has a degree-one endpoint. Those endpoints are distinct for distinct edges, and summing degrees in the cubic graph gives 4|L| ≤ 3|D|.

Lean checks all 16,384 possible vertex sets D. For each set it checks a matching outside its induced edges and every feasible missing-edge count. The independent Python census checks all 2,097,152 edge subsets directly, computes the exact minimum cover of H and tests for a path in L. Both methods give the following necessary gate counts.

| Missing edges | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 27 | 28 | 28 | 27 | 28 | 28 | 27 | 27 | 26 | 25 | 24 |

| Missing edges | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 24 | 22 | 22 | 21 | 20 | 19 | 19 | 17 | 17 | 16 | 14 |

At six losses the endpoint bound alone leaves 70 patterns at 26 gates. All 70 contain a three-edge path. Exactly six or seven losses therefore require at least 27 gates.

At eight losses and at most 26 gates, the gate count is exactly 26, the missing edges meet exactly eight vertices, and exactly five ordinary products survive. Enumerating sets of five centers and completing their uncovered edges leaves **357 distinct masks**. Bit i of a mask denotes edge i in the zero-based order in `src/HeawoodStages.lean`. The independent edge census also finds that every mask is induced on its eight vertices.

| Shape of the eight missing edges | Labeled masks | Representative mask |
| --- | ---: | ---: |
| Six-cycle with one leaf attached to each of two different cycle vertices | 168 | 383 |
| Six-cycle with a two-edge path attached at one vertex | 168 | 1899 |
| Eight-cycle | 21 | 15558 |

The independent program enumerates all 336 automorphisms of the Heawood graph. The images of each representative give its entire row of the table. This reduces the unrestricted eight-loss case to three representatives. For a prescribed opening, the relabeling also acts on the opening ports. A realization with one of these masks is still open. The sorted masks are in `census.json` under `eight_edge_masks`.

## Positive controls

The packet supplies one correct circuit for each possible loss count from zero through 21. It groups edges into the seven stars on one side of the bipartition and splits at most one star. For a positive loss count, it joins the chosen star products and ANDs the result with itself. This gate preserves the full output and suppresses exactly the desired edges upon pruning.

The zero-loss circuit uses 27 gates, attaining the corresponding lower bound. The seven positive multiples of three use 28 gates. The other fourteen counts use 29 gates. The control program checks the full and pruned outputs on all 16,384 assignments and on the 58 packed project rows. The controls use unrestricted openings. Their gate codes and lost edge indices are in `controls.json`.

## Reproduce

Use the pinned upstream project with Lean 4.36.0. From this packet directory run the following commands.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --build /tmp/heawood-125
python3 -B census.py --stages src/HeawoodStages.lean > /tmp/heawood-census.json
cmp /tmp/heawood-census.json census.json
python3 -B certificate.py --stages src/HeawoodStages.lean > /tmp/MatchingData.lean
cmp /tmp/MatchingData.lean src/MatchingData.lean
python3 -B boundary_certificate.py --stages src/HeawoodStages.lean > /tmp/BoundaryData.lean
cmp /tmp/BoundaryData.lean src/BoundaryData.lean
python3 -B controls.py --stages src/HeawoodStages.lean --statement statement.txt > /tmp/heawood-controls.json
cmp /tmp/heawood-controls.json controls.json
```

The main Lean theorems in `Checkpoint125.Heawood` are `terminalBudget`, `pathBudget`, `gateFloor`, `shortCircuits`, `postedEightLost`, `eightProfile`, `eightPatterns`, `eightList` and `eightCount`. The Lean kernel also checks the complete list of 357 masks against the five-center enumeration. The packet includes all 52 local source modules and a checksum for each module. The replay checks the reported axioms against propositional extensionality, classical choice and quotient soundness. The preceding packet is available at its immutable fork commit. [Checkpoint 124](https://github.com/perseusabbot/pequalnp-proofs/tree/1ef65435946f125502ba585e555a416d537759a6/notes/heawood-124)
