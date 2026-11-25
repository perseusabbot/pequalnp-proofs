# Ten lost Heawood edge inputs and one remaining shape at ten losses

A correct circuit of at most 26 two-input AND and OR gates for the Heawood edge function must lose **at least ten of its 21 individual edge inputs** when nested AND outputs are forced to zero. On an individual edge input, exactly the two endpoint variables equal one. An AND is nested when either operand depends on an earlier AND gate.

At exactly ten losses, the circuit must use 26 gates. Its missing edges must be a relabeling of **mask 16071**. This graph consists of three internally disjoint paths of lengths 2, 4 and 4 between the same two vertices. There are 84 labeled candidates. Whether a circuit realizes this shape in 26 gates remains open, as do the cases with more than ten losses.

| Gate limit | Checkpoint 126 lower bound on losses | Checkpoint 127 lower bound |
| ---: | ---: | ---: |
| 26 | 9 | 10 |
| 25 | 10 | 12 |
| 24 | 12 | 12 |
| 23 | 12 | 14 |
| 22 | 14 | 15 |
| 21 | 15 | 16 |

The bounds apply to shared gates, repeated operands, arbitrary output wires and the evaluator's default zero for unavailable wires. Lean derives the ten-loss result for the exact 65 prescribed openings and all four operation choices in the project's packed problem L-meta-3541 under L-meta-3004. [Posted statement](statement.txt) · [Gate floor and packed-search theorem](src/TenLossFloor.lean)

## Why all 126 previous candidates disappear

Checkpoint 126 left three shapes at nine losses. The first 56 cases contain an induced six-cycle. The other 70 contain an induced seven-vertex tree with a center and three paths of length two extending from it. This tree is called a subdivided claw. [Previous checkpoint](https://github.com/perseusabbot/pequalnp-proofs/tree/0d13f4a8b724e2fb5cfd8f740525b6769e3f10a5/notes/heawood-126)

Write h for the number of surviving edges, v for the number of vertices incident to the missing edges, j for the number of distinct retained ordinary AND products, and g for the original gate count. On inputs selecting vertices of one of the two missing graphs, all retained products vanish. The previous contraction leaves at most g − h binary gates. Its output cone contains one forced singleton label for each missing endpoint and a separate label for each of the j products.

Turning off vertices outside the chosen graph removes at least v + j − k gates, where k is the number of vertices in the graph. This follows from the zero-input deletion theorem for shared circuits. A singleton outside the graph and a product label each become zero. Other allowed inputs are disjunctions supplied by neighborhoods in the surviving graph. On a missing six-cycle, each of those inputs becomes zero or one singleton variable. On the subdivided claw, it may also become a disjunction of the three tips. Lean checks these restrictions for all 28 six-cycles and all 112 induced subdivided claws in the Heawood graph. [Projection onto the small graphs](src/PatchGeometry.lean) · [Gate accounting](src/PatchBudget.lean)

Both restricted problems need eight binary gates. Thus a missing six-cycle gives **h + v + j + 2 ≤ g**, and a missing subdivided claw gives **h + v + j + 1 ≤ g**. In each of the 126 previous candidates h = 12 and j = 4. The six-cycle cases have v = 9 and the remaining cases have v = 10. Both inequalities therefore give g ≥ 27.

## The eight-gate lower bounds

Choose a gate in the output cone with two input signals as operands. Equal operands allow the gate to be deleted. With distinct operands, cut the gate and introduce a fresh input carrying its value. The new input occurs in the residual circuit. If the original used at most seven gates, the residual circuit has at most six. A single output of six binary gates can use at most seven distinct labels. At equality its expansion is a read-once formula.

For each possible bottom gate, the certificate supplies positive and negative assignments. On each pair, every available input except one transfers truth from the positive row to the negative row, as does the cut gate. Monotonicity forces the omitted input label to occur.

| Restricted model | Distinct-operand gates checked | Seven original labels forced | Six original labels forced |
| --- | ---: | ---: | ---: |
| Six-cycle, ordinary variable inputs | 30 | 0 | 30 |
| Subdivided claw, with all disjunctions of tips available as inputs | 110 | 89 | 21 |

Seven forced original labels plus the fresh label exceed the residual budget. For each six-label case, the seven labels including the fresh one exhaust it. The certificate gives two four-row tests where the target changes from the conjunction of two distinguished variables to their disjunction. The remaining input signals, including the cut gate, are constant as those two variables vary within each test. A read-once monotone formula cannot implement the switch. The proof handles arbitrary gate order and wire sharing. Explicit eight-gate circuits attain both bounds using only singleton inputs. [Small-circuit proof](src/SmallBound.lean) · [Certificate verifier](src/SmallChecks.lean) · [Eight-gate controls](src/SmallControls.lean)

## The ten-loss orbit

A ten-loss realization at the gate limit has eleven surviving edges, nine missing-edge endpoints and four ordinary retained products. In the project's vertex numbering, the three paths of representative 16071 are

- 0–7–3
- 0–8–2–12–3
- 0–10–4–11–3

Bit i of a mask denotes edge i in the posted zero-based order. The representative has bits 0, 1, 2, 6, 7, 9, 10, 11, 12 and 13 set. Its missing graph contains two six-cycles and one eight-cycle and is induced on its nine vertices.

Lean checks the sorted list of 84 masks and an explicit vertex permutation taking the representative to each of them. Each permutation preserves adjacency in both directions. Independently enumerating all 336 automorphisms gives exactly those 84 images and a stabilizer of size four. Relabeling a circuit also relabels its opening ports, which matters when considering a prescribed opening. [Candidate masks](src/TenData.lean) · [Relabeling theorem](src/OrbitProof.lean) · [Census and representative](ten_census.json)

Restricting the representative to its nine missing endpoints gives a smaller necessary synthesis problem. The contracted circuit has at most 15 gates because eleven edges survive. All four retained product labels become zero, leaving at most **eleven gates** for the restricted function. Inspecting every surviving neighborhood gives just three additional disjunctions that can appear as inputs, in addition to the nine singleton variables. Their pairs in the original numbering are {2,4}, {8,11}, and {10,12}. A circuit realizing the full ten-loss case must meet this eleven-gate budget. An explicit thirteen-gate control computes the restricted function on all 512 assignments. Within either of the two six-cycles the available budget is exactly eight gates. The independent census records the port order, optional signals, and control circuit. [Restricted instance and control](ten_census.json)

The packet also exports this eleven-gate question in DIMACS CNF. It has 1,078 variables and 16,246 clauses. The rows are the ten individual missing edges and the eleven maximal independent sets of the nine-vertex graph. These suffice because the gates and all twelve input signals are monotone. Operand indices may coincide, and unused gates are permitted. A shorter circuit can be padded by taking the output AND itself. The model checker validates the clauses and evaluates the resulting program on all 512 assignments. CaDiCaL 2.1.2 reached its 120-second limit on the eleven-gate instance without a verdict. [Synthesis-instance exporter](restricted_search.py) · [Solver run and positive control](restricted_search.json)

## Gate floors for all 22 loss counts

| Missing edges | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 27 | 28 | 28 | 27 | 28 | 28 | 27 | 27 | 27 | 27 | 26 |

| Missing edges | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Gate floor | 26 | 24 | 24 | 23 | 22 | 21 | 21 | 19 | 19 | 18 | 16 |

For each of 16,384 possible endpoint sets, the Lean checker bounds the number of surviving product labels with disjoint surviving edges. Where the endpoint count and the path bound leave room, the checker tests which internal edges can be omitted from the lost set and applies the six-cycle, subdivided-claw or eight-cycle inequality. A supplementary matching can certify additional surviving products. At ten losses the checker proves a floor of 27 for masks outside the published list. The independent program computes exact minimum vertex covers for complements and checks all 2,097,152 missing-edge sets. [Arithmetic and membership proof](src/FloorLogic.lean) · [Kernel check](src/FloorAudit.lean)

## Reproduction

The packet includes 78 Lean modules and their checksums. Use Lean 4.36.0 with the pinned upstream project revision below. Run the commands from this packet directory.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --build /tmp/heawood-127
python3 -B small_certificates.py > /tmp/heawood-small.json
cmp /tmp/heawood-small.json small_checks.json
python3 -B small_certificates.py --lean > /tmp/SmallData.lean
cmp /tmp/SmallData.lean src/SmallData.lean
python3 -B ten_census.py > /tmp/heawood-ten.json
cmp /tmp/heawood-ten.json ten_census.json
python3 -B ten_census.py --lean patches > /tmp/PatchData.lean
cmp /tmp/PatchData.lean src/PatchData.lean
python3 -B ten_census.py --lean masks > /tmp/TenData.lean
cmp /tmp/TenData.lean src/TenData.lean
python3 -B ten_census.py --lean relabelings > /tmp/OrbitData.lean
cmp /tmp/OrbitData.lean src/OrbitData.lean
python3 -B ../heawood-125/controls.py --stages src/HeawoodStages.lean --statement statement.txt > /tmp/heawood-127-controls.json
cmp /tmp/heawood-127-controls.json ../heawood-125/controls.json
python3 -B restricted_search.py --cnf /tmp/theta-11.cnf
python3 -B restricted_search.py --gates 13 --pin-control --cnf /tmp/theta-control.cnf
cadical /tmp/theta-control.cnf > /tmp/theta-control.model
python3 -B restricted_search.py --gates 13 --pin-control --model /tmp/theta-control.model
```

The default replay also checks the two previous boundary catalogues. It audits reported axioms against propositional extensionality, classical choice and quotient soundness. The 22 full-graph control circuits cover every possible loss count, all 16,384 vertex assignments and all 58 packed rows. [Module manifest](modules.json) · [Verification record](verification.json) · [Kernel log](kernel.log)
