# Heawood circuit bounds at Checkpoint 129

Every correct Heawood circuit with at most 26 two-input AND and OR gates must lose **at least 15 of the 21 individual edge inputs**. An edge input sets exactly its two endpoints to true. It is lost if the output becomes false after forcing to zero each AND with an earlier AND anywhere among its input ancestors. The previous checkpoint established a lower bound of 12 losses. The existence of a 26-gate circuit remains open. [Previous result](../heawood-128/README.md)

Across all loss counts, the unrestricted-opening monotone circuit size is **at least 20 and at most 27**. Seven three-edge stars give the upper bound, which the frontier audit checks on all 16,384 assignments. At a gate limit of 26, the remaining 10,536 labeled edge sets fall into 63 symmetry classes. Exactly 1,078 of these sets, in seven classes, have 15 losses. Every remaining class and every labeled mask can be recovered from the published data. [Remaining masks and gate bounds](frontier.json) · [27-gate circuit](../heawood-125/controls.json)

## Three complete loss layers

| Lost edges | All sets checked | Sets passing the earlier gate inequalities | Symmetry classes | Classes requiring a new search | Sets still possible |
|---:|---:|---:|---:|---:|---:|
| 12 | 293,930 | 6,510 | 28 | 28 | 0 |
| 13 | 203,490 | 19,950 | 75 | 75 | 0 |
| 14 | 116,280 | 38,052 | 137 | 6 | 0 |

The 109 directly tested classes all fail their necessary projected gate budgets in two exhaustive programs. Each of the other 131 fourteen-loss classes would supply a circuit for one of those same tests. Lean checks the reduction from an arbitrary correct circuit for all 240 representative tables, including the project’s 65 posted openings with each of the four gate-operation choices. The exhaustive gate searches and the symmetry-class census run outside the Lean kernel. The standalone global loss theorem previously proved entirely in Lean gives 11 losses. [Representative theorem](src/BoundaryAudit.lean) · [Finite checks](results.json) · [Previous kernel theorem](../heawood-128/src/ElevenLoss.lean)

## Why projection pays for deleted vertices

Let the lost-edge set be $M$, let $h=21-|M|$, and let $v$ count the endpoints of edges in $M$. Choose a matching of $j$ surviving edges. Retaining those edges requires at least $j$ distinct ordinary products. Now restrict to a vertex set $T$ among the lost endpoints and set every outside vertex to false.

The contracted output depends on a separate singleton signal for each of the $v$ endpoints, as well as on the retained products. On a lost two-endpoint input or a negative assignment, every retained product is false. Each forced singleton outside $T$ is false as well. Removing these inputs from the binary circuit saves at least one gate per distinct removed label. For an original circuit of size $g$, a circuit for the sampled rows must therefore exist within the following budget. [Projection proof](src/ProjectedBoundary.lean)

$$
g-h-j-(v-|T|).
$$

The positive rows are the lost edges lying inside $T$. The negative rows are the maximal independent sets of the full Heawood graph induced on $T$. The allowed inputs are its singletons and all nonempty disjunctions drawn from the surviving neighbors of a single original vertex. Supplying all these disjunctions for free makes an exclusion apply to the original circuit even when the sample contains surviving edges. [Row construction](instances.py) · [Kernel checks](src/ProjectedScreen.lean)

For a transferred test, an incidence-preserving relabeling maps the old sampled vertices to the new sample. The available signal masks are contained in the old palette, all old required positives are still required, and the maximal negative rows coincide. The new circuit must pass the old test whenever its projected budget fits the old cap. The fourteen-loss Lean tables retain the source cap, signal masks and rows literally and check each new matching and vertex assignment. [Transferred tables](transfers.json) · [Transfer audit](src/TransportAudit.lean)

## Two exact restricted functions

| Lost-edge mask | Sample vertices | Allowed signals | Budget | Exact minimum |
|---:|---:|---:|---:|---:|
| 32711 | 10 | 13 | 14 | 15 |
| 32751 | 10 | 11 | 15 | 16 |

The first sample is the graph obtained by subdividing every edge of $K_4$ once. Its ten singleton inputs and three additional free pair disjunctions still require 15 gates. Four three-edge stars attain the minimum. The second sample has twelve edges and one free pair disjunction. Five stars attain its 16-gate minimum. All internal edges are lost in both samples, so monotonicity extends the positive-edge and maximal-negative tests to every assignment. Lean also evaluates both displayed circuits independently on all 1,024 assignments each. [Four-star circuit](k4.json) · [Five-star circuit](five_stars.json) · [Kernel audit](kernel.log)

For mask 32751 the first checker visited 12,606,086 states at 15 gates. The independent checker expanded 11,502,372. It reconstructed the graph, inputs and rows directly from the two integer masks. [Both decisions](results.json)

## Bounds beyond the first three layers

| Lost edges | Gate lower bound | Classes still possible at 26 gates | Labeled sets still possible |
|---:|---:|---:|---:|
| 15 | 25 | 7 | 1,078 |
| 16 | 25 | 14 | 3,003 |
| 17 | 25 | 26 | 4,893 |
| 18 | 23 | 11 | 1,330 |
| 19 | 23 | 3 | 210 |
| 20 | 22 | 1 | 21 |
| 21 | 20 | 1 | 1 |

If a source test on $t$ vertices fails at $k$ gates, every compatible original circuit needs at least $h+j+v+k+1-t$ gates. The frontier audit checks the palette and positive and negative rows for each chosen source and computes this bound for every remaining representative. A circuit with 20 or 21 gates would have to lose all 21 individual edge inputs. At 15 losses, six of the seven remaining classes need at least 26 gates. Representative 128895 has the current lower bound of 25 gates. [Class bounds and exact mask lists](frontier.json)

## Exhaustive checks and reproduction

The last-use checker enumerates separating input supports of size at most one more than the gate cap. After each binary gate it tests all four possibilities for subsequent uses of the operands. A positive/negative row pair must be separated by at least one live signal. States retain multiplicities when different wires have identical evaluations. The optional positive node limit in the diagnostic executable returns an explicit undecided result. The verifier runs every case without a node limit. [Last-use checker](live_search.cpp)

The availability checker retains all current signals after adding a gate. It enumerates all sufficiently large supports allowed by the binary leaf bound and may discard signals unrelated to the gate operands. For a minimum circuit the new signal must occur in its continuation. Recomputing a signal already present, or introducing a constant on the sample, cannot shorten such a circuit. Both checkers compare complete states in their memo tables. Twelve small controls check both positive and negative decisions against a third, unpruned enumeration. [Availability checker](available_search.cpp) · [Numerical verifier](verify.py)

The census tests the earlier cycle, claw, path and matching bounds on every mask in the stated layers. It independently computes maximum matching and minimum vertex cover on all $2^{21}$ subsets. A second orbit audit represents the Heawood graph as the incidence graph of the Fano plane. It uses the 168 invertible linear maps on three binary coordinates and incidence duality to generate all 336 graph automorphisms. It checks orbit sizes and disjointness, then reconstructs the SHA-256 digest of the original sorted candidate masks in every layer from 12 to 21. Edge bit $i$ always denotes entry $i$ of the posted zero-indexed edge list. Each digest uses three little-endian bytes per mask. [Fano plane audit](frontier.py) · [Posted edge order](../heawood-127/src/HeawoodStages.lean)

Run these commands from this directory with Python 3 and a C++17 compiler.

```sh
python3 -B ../heawood-128/verify.py
python3 -B generate_lean.py
python3 -B verify.py
python3 -B frontier.py
```

For the Lean replay, prepare the upstream project at revision `048b39bb2c5b2c21da06d44218d16366086a68d9` with its Lean 4.36.0 toolchain and Mathlib dependencies. The replay authenticates the previous modules, rebuilds the extension, and audits the theorem dependencies.

```sh
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/heawood-129 --jobs 2
```

The committed source manifest and build receipt record the inputs and the scope of the checks. [Source manifest](sources.json) · [Verification receipt](verification.json)
