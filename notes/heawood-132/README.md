# Heawood circuit bounds at Checkpoint 132

Any circuit with at most **25 gates must lose at least 20 of the 21 Heawood edge inputs**. Just 22 labeled loss sets remain at that budget, down from 78 in four classes at Checkpoint 131. The 14 labeled 18-loss stars and the 42 labeled members of 19-loss class 524287 account for the reduction. At 26 gates, 246 sets in six symmetry classes remain. The unrestricted minimum is between 24 and 27 gates. The posted question L-meta-3541 asks for a circuit with at most 26 gates and one of 65 prescribed openings. It remains open. [Class inventory](frontier.json) · [Previous checkpoint](../heawood-131/README.md)

## The three surviving edges

An edge input sets exactly its two endpoints to true. To count losses, force an AND to zero whenever it has an earlier AND among its input ancestors. An edge input is lost if the resulting circuit rejects it.

At exactly 18 losses there is one possible shape. Its three surviving edges meet at a single vertex. Use vertex 6 as the center and vertices 8, 9, 11 as its neighbors. Removing the center leaves 18 positive edge rows and 30 maximal independent rows. An exhaustive search gives a lower bound of 22 local gates even when all three neighbor pairs and the triple are free OR inputs. The search exhausted eight initial supports and 3,061,063 states. [Signed decisions](results.json) · [Local row table](src/StarBudget.lean)

Let $b$ count the actual pure OR gates with regular supports and let $j$ count the distinct surviving products. A support is regular if it is empty, a singleton, or contained in the retained neighborhood of one vertex. Three retained edges give $3\le b+j$ and require $j\ge1$. A boundary circuit of size $L$ satisfies $b+2j+L\le g$, where $g$ is the original size. One charge for each product comes from constructing it. The second comes from removing its distinct, used label on the boundary rows. With $L\ge22$ and $g\le26$, equality forces $g=26$, $b=2$ and $j=1$. [Projection with exact costs](src/RetainedCost.lean) · [Equality proof](src/StarBudget.lean)

The single product must be the center AND the OR of its three neighbors. The two regular gates build one neighbor pair, followed by its union with the third neighbor. Lean therefore reduces a 26-gate circuit of this shape to a circuit with **22 gates and 15 available inputs**. Those inputs are the 13 surviving singletons, the pair actually built, and the triple. The three pair choices are equivalent under graph symmetries. [Product and OR shape](src/StarShape.lean) · [15-input necessity theorem](src/StarRestriction132.lean) · [Three relabelings](completion.json)

## Connection to the posted opening

Choose the pair 8, 9. After relabeling, the first gate computes $x_0\lor x_1$ on wire 14. The second computes $x_3\lor w_{14}$ on wire 15. This is posted opening **20** (zero-based), key **284**, with both flags true. The center becomes vertex 7. After the local computation, add $x_7\land w_{15}$ and OR it with the local output. A local program of length $k$ gives $k+4$ total gates and $k+2$ operations after the opening. [Executable translation](completion.py)

Lean proves that a local program of at most 22 gates, expressed in the posted wire numbering and avoiding the deleted center, gives an actual posted witness whenever its local packed output is 262143. The bridge checks the 18 nonstar positive rows, covers all 37 full negative rows by local negative rows, and proves the high output bits vanish. An explicit 23-gate local circuit exercises the same construction. It gives the required posted word 2097151 at 27 total gates, with 25 operations after the opening. The posted tail cap is 24. [Posted-witness theorem](src/OpeningLift132.lean) · [Kernel-checked control](src/OpeningControl132.lean)

## Bounds across loss counts

| Lost edges | Gate lower bound | Labeled sets possible at 25 gates | Labeled sets possible at 26 gates |
|---:|---:|---:|---:|
| 15–17 | 27 | 0 | 0 |
| 18 | 26 | 0 | 14 |
| 19 | 26 | 0 | 210 |
| 20 | 25 | 21 | 21 |
| 21 | 24 | 1 | 1 |

The 13-vertex bound also gives 26 gates for the 19-loss representative 524287. A separate 12-vertex test gives an independent route to the existing 26-gate bounds for representatives 917503 and 1015807. Its exact cost is 20. Its lower-bound search exhausted 7,443,710 states, and an explicit circuit attains 20 on all 4,096 assignments. Charging two retained edges, a matching of size two and two outside vertices gives $20+2+2+2=26$ in each case. The census verifies the transfers and labeled orbits under all 336 graph automorphisms. [Class-by-class transfers](frontier.json) · [Explicit circuits](controls.json)

## Unconditional Lean lower bound

Lean now proves **20 gates unconditionally** for the original full-graph instruction list. The preceding kernel bound was 19. The proof cuts a first nontrivial gate, chooses an induced subgraph, and counts the labels that become constants and still have to occur in the remaining circuit. In some restrictions one deleted vertex can be set true because it has no neighbor in the retained subgraph. That choice can make the cut gate constant and save another gate. Fifteen induced graphs and 89 placements cover every choice of the operation and both operands. A posted witness consequently requires at least 18 operations after its opening pair by the kernel argument alone. [Deletion proof](src/InducedCut.lean) · [Checked placements](deletions.json) · [Original-program theorem](src/InducedProgram.lean)

A second deletion proof reduces a 21-gate bound to four finite searches on graphs with eight or nine vertices. Their exact costs are 11, 11, 12 and 13. A signed-row recurrence, a last-use search and an independent availability search agree on all four. Lean verifies the reduction and the signed encodings. The four negative search decisions are external. The stronger full-graph bound of 24 also uses the preceding checkpoint's numerical work. [Four decisions](results.json) · [Conditional 21-gate theorem](src/SeedProgram.lean)

## Numerical verification

The signed engine enumerates last uses of live wires. Each local restriction has a verified row embedding and a previously established gate floor. The search may rebuild each current live signal from constants, local inputs, or an expression with one or two gates. Combining these costs gives an upper bound on the cost of a shared prefix. Any live signal represented by a constant saves a gate in the suffix. The engine uses the tighter of this budget and the budget obtained by translating the actual prefix. [Search implementation](symmetry_search.cpp) · [Signed embeddings](projections.json) · [Shared-prefix theorem](../heawood-131/src/RebuiltPrefix.lean)

The engine checks each input permutation on both signed row sets. After a gate, it uses only permutations preserving that gate and its retained operands. Its compact memo table records the live column set and the depth. To see why this suffices, take the earliest canonical minimum circuit. At a repeated state, its suffix could follow the earlier prefix with identical columns. The resulting circuit has the same truth on every row. Removing unused gates would contradict minimality, and the suffix can be put into canonical order under the earlier prefix's remaining symmetries. This would give an earlier minimum circuit. The optional reference search keeps every restriction's allowance in the key and translates the actual prefix throughout. [Checker and reference option](check.py)

The 43 signed decisions expanded 10,614,558 states. The release also checks 99 small solver controls, rejects seven damaged symmetry or embedding descriptions, verifies 46 local constructions on 58,624 assignments, and evaluates each of the three lifted 27-gate controls on all 16,384 full assignments. [Numerical results](results.json) · [Verification receipt](verification.json)

Run the following from this directory with Python 3 and a C++17 compiler. The Lean replay uses version 4.36.0, Mathlib, and upstream revision `048b39bb2c5b2c21da06d44218d16366086a68d9`. To test a candidate, pass a JSON list of `["AND" or "OR", left, right]` gates to `completion.py --circuit FILE`. Inputs 0 through 12 are the surviving singletons in vertex order. Inputs 13 and 14 are the chosen pair and the triple. Each gate appends a wire, and the last wire is the output.

```sh
python3 -B deletion_tables.py
python3 -B seed_tables.py
python3 -B completion.py
python3 -B check.py --jobs 2
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/heawood-132 --jobs 2
```

Running `python3 -B reduced_search.py` starts the remaining 22-gate search with the reduced input list. It verifies and translates any circuit it finds into posted instructions. The `--emit` option writes the validated input instance. The `--cap 21` control reproduces the established lower bound immediately. [Reduced search](reduced_search.py)
