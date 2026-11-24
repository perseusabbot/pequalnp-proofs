# Optimal three-stage circuits for the Heawood edge predicate

On the fourteen inputs of the Heawood graph, the target is true when both endpoints of an edge are true. In the OR–AND–OR circuit model, every optimum uses 27 gates. The bottom stage uses 14 ORs, the middle uses seven ANDs and the top uses six ORs. This model allows sharing and unused gates. The proof classifies the bottom stage of every physical circuit within that budget.

The centers of the seven AND gates are either all seven Fano points or all seven Fano lines. Each gate takes its center and the OR of its three neighbors. Building a triple requires an intermediate pair. Two different neighborhoods meet in at most one vertex, so no intermediate pair can serve two stars. Lean proves that the seven pairs and seven triples account for every bottom gate and that all fourteen supports are distinct. [Physical circuit classification](src/BottomPairs.lean) · [Star centers and gate counts](src/OptimalStars.lean)

There are **4,374 possible sets of bottom-stage supports**. Either vertex class can serve as the centers, and each of the seven stars admits three choices for the first pair. The independent circuit evaluator constructs a 27-gate realization of every choice and checks its output on all 16,384 assignments. Different gate orders or top-stage OR trees can realize the same set of bottom supports. The upstream project asks whether an unrestricted monotone circuit can use 26 gates. That question remains open. [Heawood project reduction](https://github.com/open-goat/pequalnp-proofs/pull/7218)

## Cubic graphs

For a nonempty graph of girth at least five, the exact minimum price of the three-stage star representation is the edge count plus the minimum vertex-cover size minus one. The family includes the physical shared OR–AND–OR circuits used above. For the cubic graph problem L-meta-2084, a second theorem shows that converting arbitrary signed circuits to the representation at the same cost is equivalent to the proposed full lower bound. PR 7620 has the reduction. Its two already proved child statements remove isolated marked inputs and bound the cost of the representation. The signed-circuit conversion remains open. [Exact representation cost](src/Sharp.lean) · [Equivalence with the remaining subproblem](src/ExactReduction.lean) · [Project reduction](https://github.com/open-goat/pequalnp-proofs/pull/7620)

## Reproduce the results

From this directory, the following commands verify the sources against `modules.json` and rebuild both families. Install `elan` with `lake` on the path and use a separate checkout at the linked project's pinned revision. The exported Lean reports are in `heawood-kernel.log` and `cubic-kernel.log`.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --packet . --build /tmp/heawood-replay --jobs 2 --resume
python3 -B layouts.py --stages src/HeawoodStages.lean
```

The last command reproduces `layouts.json`, including the SHA-256 digest of the sorted support families. The local results build on the earlier project and checkpoint modules included in `src`. The source for the checked L-meta-2535 lemma is preserved byte for byte from the upstream project. The project sources are distributed under the repository's Apache 2.0 license. [Upstream L-meta-2535](https://github.com/open-goat/pequalnp-proofs/blob/048b39bb2c5b2c21da06d44218d16366086a68d9/lean/PEqualNP/Outside/L_meta_2535.lean)
