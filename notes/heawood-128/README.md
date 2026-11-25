# Heawood circuits require at least twelve pruning losses

The finite searches in Checkpoint 128 show that a correct Heawood circuit with at most 26 two-input AND/OR gates must lose **at least twelve of its 21 individual edge inputs** when nested AND gates are forced to zero. On an individual edge input only its two endpoints are true. An AND is nested when at least one of its operands depends on an earlier AND. Whether a correct circuit of this size exists remains open.

Lean proves the **eleven-loss** lower bound for arbitrary circuits and for the 65 prescribed openings and all four opening-operation choices in L-meta-3541. Two independently implemented exhaustive searches establish the **twelve-loss** lower bound. Lean also proves the gate-budget reduction for each of the seven eleven-loss representatives. The eleven-loss pattern census and the final seven search outcomes are verified by executable enumeration. [Lean theorem for the posted problem](src/ElevenLoss.lean) · [Seven representative budgets](src/ScreenProof.lean) · [Reproduction record](verification.json)

## The nine-vertex graph needs exactly thirteen gates

Checkpoint 127 reduced all 84 ten-loss possibilities to a graph with three internally disjoint paths of lengths 2, 4 and 4 between the same vertices. A 26-gate realization could spend at most eleven gates on this restricted function. Its available inputs were nine singleton variables and three disjunctions, each of two variables. The SAT run at that checkpoint timed out. [Checkpoint 127](../heawood-127/README.md)

Each positive row is an individual edge. Each negative row is a maximal independent set. There are ten positive and eleven negative rows. A monotone output that passes these rows computes the function on all 512 assignments. The searches exclude circuits with twelve gates, including any smaller circuit. An explicit thirteen-gate circuit passes all 512 assignments and its operands are checked in Lean. This gives an exact minimum of **13**, two gates over the budget. [Search results](theta_search.json) · [Checked upper bound](src/ThetaPorts.lean)

The kernel replay separately exhausts the eleven-gate search on all eight possible input supports. For any of the 84 embedded copies whose internal edges are missing, it proves

`surviving edges + missing-edge endpoints + retained products + 12 ≤ original gates + 9`.

At exactly ten losses, Checkpoint 127 gives 11 surviving edges, 9 incident vertices and 4 retained products. Substitution requires at least 27 gates. [Projection theorem](src/ThetaTransfer.lean) · [Eleven-gate search audit](src/ThetaAudit.lean)

## How the two exhaustive searches work

A signal separates a positive/negative row pair when it is true on the positive row and false on the negative row. Every pair must be separated by at least one live signal. Otherwise monotonicity prevents every future output from distinguishing that pair.

The Python search keeps the signals actually used by the remaining circuit. It cuts a gate with two terminal operands and gives the computed value a fresh label. Each original operand can disappear or remain available for another use, giving four choices. If the original gate cap was k, the residual circuit has at most k − 1 gates and uses at most k distinct terminal labels. The checker discards states that exceed that limit or lose a required row distinction. It preserves multiplicity when two labels have the same row values. Repeated uses of one operand at the same gate can be collapsed by idempotence. Lean proves that any successful circuit has a path through this search. For the twelve-gate theta test, Python checks 56,238 distinct states. [Completeness proof](src/ThetaSound.lean) · [Python search](theta_check.py)

The C++ search starts from every freely available signal and independently constructs its test rows from the Heawood edge list. When the available set is too large, a circuit must omit some signal. The search tries each omission that preserves separation. Once the available set fits the terminal budget, it tries every pair and operation, adds the resulting signal, and reduces the gate cap. A minimum circuit never needs to recreate a signature already available on the tested rows. This search expanded 3,016,932 states on the twelve-gate theta test. A single-edge control was accepted at one gate and rejected at zero. [C++ search](availability.cpp) · [Results and controls](availability.json)

## Why eleven losses are also impossible

There are 352,716 ways to choose eleven missing Heawood edges. For each complement, the census computes the exact maximum matching size and checks it against the exact minimum vertex cover size. A matching lower-bounds the number of retained products because each retained ordinary product covers a star in the square-free Heawood graph. The endpoint, path, cycle and subdivided-claw inequalities from Checkpoint 127 leave 1,176 candidates. Enumerating all 336 Heawood automorphisms partitions these into seven orbits. The propagation of costs and row signals is invariant under simultaneous relabeling of the circuit inputs and graph. [Census and orbit computation](boundary.py)

For each representative, turn off all vertices outside the missing-edge endpoints. Use its eleven missing edges as positive rows and the maximal independent sets of the **whole induced Heawood graph** as negative rows. This choice matters when a surviving edge joins two sampled vertices. All retained products are zero on these rows. Every surviving regular input is zero, a singleton, or an OR over a subset of one vertex's surviving neighbors on the sampled vertices. The model gives every such OR to the circuit for free. Ten edges survive, and each distinct retained product pays for another gate when its zero input is deleted from the dependency cone. Lean checks the resulting gate caps, signal palettes, positive rows, negative rows and surviving matchings at the seven representatives. [Boundary-row reduction](src/BoundaryRows.lean) · [Finite representative checks](src/ScreenProof.lean)

| Missing-edge mask | Labeled patterns | Sampled vertices | Surviving edges among them | Free signals | Negative rows | Gate cap |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3071 | 168 | 10 | 0 | 16 | 12 | 12 |
| 14206 | 168 | 11 | 2 | 17 | 18 | 11 |
| 15583 | 168 | 11 | 1 | 23 | 21 | 12 |
| 16079 | 84 | 10 | 0 | 16 | 14 | 12 |
| 16327 | 168 | 10 | 1 | 13 | 12 | 12 |
| 19451 | 84 | 10 | 0 | 14 | 13 | 12 |
| 23471 | 336 | 10 | 1 | 12 | 14 | 12 |

Both searches exhaust every representative at its gate cap. Across the seven tests the Python search checks 39,160 states and the C++ search expands 2,526,475. A separate 21-gate positive control computes each missing-edge function on every assignment of its sampled vertices, totaling 9,216 assignments. The complete list of labeled candidates and the row masks for each representative appear in the census. [Boundary results](boundary.json)

## Reproduction

Run from this directory with Python 3 and a C++17 compiler. The commands regenerate the data and compare both exhaustive searches with their saved outputs.

```sh
python3 -B generate_data.py
python3 -B verify.py
```

For the kernel proof use Lean 4.36.0 and upstream revision `048b39bb2c5b2c21da06d44218d16366086a68d9`. The replay authenticates the source files and dependencies and audits the printed theorem axioms.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --build /tmp/heawood-128 --jobs 2
```

The repository's sibling Checkpoint 127 directory supplies the prior proof sources. Its own replay also uses the earlier checkpoint directories for the corresponding historical records. [Extension source hashes](sources.json) · [Kernel audit](kernel.log)
