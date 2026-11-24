# Heawood circuits with two prescribed gates

The Heawood graph has fourteen vertices and twenty-one edges. Its edge predicate accepts an assignment when some edge has both endpoints true. Project gap L-meta-3541 asks for a monotone circuit with at most twenty-six gates. It prescribes the first two pairs of operands through a table of sixty-five representatives and allows either AND or OR at each gate. The general twenty-six-gate existence question remains open. [Posted statement](statement.txt)

## What a twenty-six-gate circuit would have to do

Call an AND gate nested if either input depends on an earlier AND, even through a chain of ORs. Replace every nested AND output with zero and leave the remaining wiring in place. Let k count the replaced gates and let m count the positive two-vertex assignments the resulting circuit loses. Lean proves the following for every program that would solve the posted instance.

- At least one nested AND can reach the output through OR gates alone.
- At least three of the twenty-one positive edge assignments are lost. More precisely, 3(k + 3) ≤ 4m.
- If exactly three edges are lost, all three share one vertex. The original circuit uses exactly twenty-six gates and has exactly one nested AND. Its surviving output contains six distinct products of input disjunctions. Twelve ORs join pairs of wires that are both free of AND ancestors. Six ORs join pairs in which both wires have an AND ancestor. The number of ANDs on two AND-free wires and the number of ORs with just one AND-free input sum to seven.

The proof records the supports of ORs, tags ordinary AND products, and tracks an additional tag for a nested AND. For a graph without four-cycles, every clean product covers a star. Each surviving Heawood product therefore covers at most three edges. If e edges survive through j distinct products and b bottom ORs, e ≤ j + b. Tracking which products can feed the final ORs accounts for sharing. A lost positive assignment requires an extra ordinary product or an OR joining an AND-free wire to a wire with an AND ancestor. These counts give the inequality above. The result allows interleaved gates, shared wires, unused gates, and the posted zero default for out-of-range input indices.

## The first two gates of a three-stage optimum

Among the 260 combinations of a representative and two gate operations, exactly five can begin a 27-gate optimum in the ordered OR–AND–OR model. Both operations are OR in each case. Wire 14 is the result of the first gate. The compatible-library count records the choices of an intermediate pair for each of seven stars.

| Representative (zero-based) | Desk key | First OR | Second OR | Compatible support libraries |
| --- | --- | --- | --- | ---: |
| 1 | 227 | 0, 1 | 0, 2 | 243 |
| 8 | 258 | 0, 1 | 2, 3 | 243 |
| 9 | 259 | 0, 1 | 2, 4 | 243 |
| 10 | 260 | 0, 1 | 2, 5 | 243 |
| 20 | 284 | 0, 1 | 3, 14 | 729 |

Lean checks necessity for physical three-stage circuits and evaluates a concrete 25-gate tail after each of these two-gate prefixes. Each gives the target word 2097151. A separate evaluator checks the five controls on all 16,384 vertex assignments. [Controls and counts](prefixes.json)

## A finite search for a shorter circuit

For each of the 1,701 compatible representative and library combinations, the search constructs one gate ordering. After the two forced ORs it builds remaining pairs and triples by center, emits the seven products in center order, then joins them from left to right. It removes one of the last twenty-five gates and redirects all later reads of its output to one earlier wire or to zero. It then replaces any one other tail gate with an AND or OR on any two available wires. The original two gates stay fixed. All surviving gate dependencies are renumbered implicitly. If the final gate is removed, the new output is the last surviving gate.

There were 24,851,065,680 choices of these edits, counted with multiplicity. None produced the posted word. For each possible replacement location the C++ evaluator computes the downstream output with that wire set to zero and to one. On each input row the downstream function is monotone in that one bit, so the two evaluations determine its value for every replacement. The resulting screen left 8,505,347,166 choices for explicit comparison. A positive control with a redundant twenty-eighth gate had 76 successful reductions to twenty-seven. This search covers the stated edits and canonical orders. The Lean lower-bound argument applies to arbitrary programs in the posted model. [Search results](repairs.json)

## Reproduction

The sources use Lean 4.36.0 and upstream project revision 048b39bb2c5b2c21da06d44218d16366086a68d9. The src directory includes the dependencies in modules.json. From this notes directory, run the following commands with the pinned checkout available at /tmp/heawood-project. The finite search also needs a C++17 compiler.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --packet . --build /tmp/heawood-122 --jobs 2
python3 -B prefixes.py --stages src/HeawoodStages.lean
python3 -B repairs.py --stages src/HeawoodStages.lean
```

PostedModel.instance_exact states that the compact instance and the desk's original proposition reduce to identical terms. Checkpoint122.Posted.postedNecessary relates the exact packed word to the pruning bound. Checkpoint122.Pruning.threeLost proves the common-vertex result. Checkpoint122.Prefix.physicalPrefix and Checkpoint122.Prefix.certificates establish the prefix classification and its positive controls.

The source of the upstream packed-row theorem is included at its pinned revision. The source of each previous checkpoint lemma is preserved in the module manifest. [Upstream packed-row theorem](https://github.com/open-goat/pequalnp-proofs/blob/048b39bb2c5b2c21da06d44218d16366086a68d9/lean/PEqualNP/Outside/L_meta_3008.lean) · [Prior Heawood classification](https://github.com/perseusabbot/pequalnp-proofs/tree/5f57c86b3058763f44084a32b17bfce891604c8e/notes/cubic-heawood-121)
