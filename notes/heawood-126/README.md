# Nine lost edge inputs in a 26-gate Heawood circuit

A correct circuit for the Heawood edge function with at most 26 two-input AND and OR gates must lose **at least nine of its 21 individual edge inputs** when every nested AND is forced to zero. On an individual edge input, exactly the two endpoints have value one. An AND is nested if either operand depends on an earlier AND.

Checkpoint 125 left 357 possibilities at eight losses. Each contains an induced six- or eight-cycle, and the cycle bound proved here excludes all 357. At exactly nine losses there are 126 candidate masks. Whether any of them is realizable, and whether any correct 26-gate circuit exists, remain open. [Checkpoint 125](https://github.com/perseusabbot/pequalnp-proofs/tree/1900111be1bb2f9476657f7dbc9217c7d3b42734/notes/heawood-125)

| Gate limit | Previous lower bound on losses | New lower bound |
| ---: | ---: | ---: |
| 26 | 8 | 9 |
| 25 | 9 | 10 |
| 24 | 10 | 12 |
| 23 | 12 | 12 |
| 22 | 12 | 14 |
| 21 | 14 | 15 |

The bounds allow wire sharing, repeated operands, arbitrary output wires and the evaluator's default zero for an unavailable operand. Lean also applies them to the project's packed search L-meta-3541 under L-meta-3004, with all 65 prescribed first pairs and all four choices of their gate operations. [Posted statement](statement.txt)

## Why losing a cycle costs another gate

Let H be the surviving edges, L the missing edges, D their incident vertices, j the number of distinct ordinary AND products represented at the pruned output, and g the original gate count. If L contains every edge of an induced six- or eight-cycle, then

**|H| + |D| + j + 1 ≤ g.**

To see the extra cost, consider assignments on which all retained products are false. The previous contraction leaves a shared circuit with at most g − |H| binary gates. Its inputs must include the singleton variable for each vertex in D and a separate zero-valued label for each of the j retained products. Write n = |D| + j. Suppose that the contracted circuit has at most n gates.

* If exactly those n labels occur, restrict all vertices outside the missing cycle to zero. Every forced label except the cycle variables now has value zero. In a binary circuit whose restricted output survives, deleting distinct zero input labels removes at least that many gates, even when gates are shared. Thus a cycle on k vertices would have a circuit with at most k gates.
* The restricted cycle predicate needs at least k + 1 gates. Each cycle variable remains essential after any other variable is fixed to either value. To prove the general bound for this property, take a bottom gate with distinct inputs, replace it by a fresh variable, and remove the gate. All k original input labels must still occur. For either input of the removed gate, fixing its partner to the controlling value makes the gate constant while the function still distinguishes that input. The fresh label also occurs. The resulting circuit therefore needs k + 1 labels, one more than a circuit with at most k − 1 gates can have. A bottom gate with equal inputs can simply be deleted.
* If an additional label occurs, the contracted circuit has exactly n gates and n + 1 distinct labels. Expanding its output then gives a read-once formula. On each missing cycle there is a three-edge path a–b–c–d on which the extra label is a singleton, a constant, or depends only on the outer vertices. With a and d both zero, the output on b and c is their conjunction. With a and d both one, it is their disjunction. A monotone formula in which b and c each occur once cannot make that switch. Lean checks the path choices and the two-variable truth tables.

The cycle restriction and the path restriction use only assignments on which all retained products are false. For the cycle bound, Lean checks the geometry of 28 induced six-cycles and 21 induced eight-cycles. An independent program enumerates the cycles directly from the graph. [Cycle proof](src/CycleBudget.lean) · [Geometry](src/CoreGeometry.lean) · [Shared-circuit gate bound](src/CherryBound.lean) · [Zero-input deletion](src/ZeroPruning.lean)

## The nine-loss boundary

Exactly nine losses at or below the gate limit require 26 gates and four distinct ordinary products. The twelve surviving edges are the union of four edge-disjoint, complete three-edge stars. If the missing edges meet nine vertices, they contain a certified cycle. If they meet ten vertices, they contain none of the 49 certified cycles. Enumerating sets of four star centers gives the following candidates.

| Missing graph | Labeled masks | Representative mask |
| --- | ---: | ---: |
| Six-cycle with a leaf attached to each of three alternating vertices | 56 | 511 |
| Three paths of length three meeting at one endpoint | 56 | 3574 |
| One center with three neighbors, each having two additional leaves | 14 | 3647 |

Lean proves that every nine-loss realization must occur in the published, strictly increasing list of 126 masks. The independent program computed the images of each representative under all 336 graph automorphisms. They cover all 126 candidates, and each candidate is induced on its incident vertices. Bit i selects edge i in the project's zero-based edge order. For an opening prescribed by the posted search, a relabeling also acts on the opening ports. [Mask list](src/NineData.lean) · [Classification theorem](src/NinePatterns.lean) · [Orbit representatives and edges](cycle_census.json)

## Gate bounds at every loss count

| Missing edges | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 27 | 28 | 28 | 27 | 28 | 28 | 27 | 27 | 27 | 26 | 25 |

| Missing edges | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 25 | 23 | 23 | 22 | 21 | 20 | 20 | 18 | 18 | 17 | 15 |

For each of the 16,384 possible vertex sets D, the Lean checker uses a matching of surviving edges to lower-bound j. When that bound and the previous path result leave room below the claimed floor, it tests each admissible deletion from the edges internal to D. For each such deletion, it exhibits a cycle lying entirely in the resulting set L. A separate calculation enumerates all 2,097,152 subsets of the 21 edges, computes the exact minimum vertex-cover size of each complement and reproduces the same floors. [Numerical proof](src/CycleNumbers.lean) · [Gate theorem and posted search](src/NineLossFloor.lean)

## Reproduce the results

The packet includes 64 Lean modules and a source checksum for each. Use Lean 4.36.0 and the upstream proof repository at commit `048b39bb2c5b2c21da06d44218d16366086a68d9`. From this packet directory, run the following commands.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --build /tmp/heawood-126
python3 -B cycle_census.py > /tmp/heawood-126-census.json
cmp /tmp/heawood-126-census.json cycle_census.json
python3 -B cycle_census.py --lean-cycles > /tmp/CycleData.lean
cmp /tmp/CycleData.lean src/CycleData.lean
python3 -B cycle_census.py --lean-nine > /tmp/NineData.lean
cmp /tmp/NineData.lean src/NineData.lean
python3 -B ../heawood-125/controls.py --stages src/HeawoodStages.lean --statement statement.txt > /tmp/heawood-126-controls.json
cmp /tmp/heawood-126-controls.json ../heawood-125/controls.json
```

The default replay builds the nine-loss theorems and rechecks the earlier 357-mask catalogue. It audits the axioms of the reported declarations and allows propositional extensionality, classical choice and quotient soundness. The 22 control circuits exercise every possible loss count on all 16,384 assignments and the 58 packed project rows. [Module checksums](modules.json) · [Verification record](verification.json) · [Kernel output](kernel.log)
