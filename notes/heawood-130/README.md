# Heawood circuit bounds at Checkpoint 130

The full Heawood edge function requires **at least 23 and at most 27** two-input monotone AND or OR gates, with unrestricted fanout, depth and opening gates. The previous lower bound was 20. At 26 gates, 2,500 labeled loss sets in 25 symmetry classes remain, down from 10,536 sets in 63 classes. The project's question about a 26-gate circuit with a prescribed opening remains open. [Previous checkpoint](../heawood-129/README.md) · [Class inventory](frontier.json)

An individual edge input sets exactly the two endpoints of an edge to true. It is lost if the circuit stops accepting it when every AND with an earlier AND among its input ancestors is forced to zero. The known lower bound at 26 gates is 15 losses. At exactly 15 losses, two classes remain. A 23-gate circuit would have to lose all 21 edge inputs. [Gate bounds by class](frontier.json)

## A six-gate reduction

Take a bottom gate of a correct circuit after removing repeated-operand gates. Its two operands are distinct vertices. Cut out the gate and supply its value as a new input. Every original vertex remains necessary in the continuation. To change one vertex while holding another fixed, use a neighbor of the changing vertex that is distinct from and nonadjacent to the fixed vertex. The Heawood graph supplies such a neighbor for every ordered pair. [Lean reduction](src/TwentyTwo.lean)

The kernel checks 28 embeddings of the same ten-vertex test. Together, their four-vertex complements contain every possible operand pair. Choose one that contains both operands and set all four outside vertices to zero. The fresh gate input also becomes zero. These five distinct labels occur in the continuation, and deleting them saves at least five gates. Including the gate already cut out, a circuit with $g$ gates supplies one with at most $g-6$ for the ten-vertex test. This counting argument allows shared gates. [Embedding cover](src/FiveEmbeddings.lean) · [Constant pruning](src/ConstantPruning.lean)

The ten-vertex test permits its ten singletons and one free disjunction. Its exact minimum is 16 by the two Checkpoint 129 exhaustions and an explicit upper-bound circuit. This gives the 22-gate bound. Lean proves the implication from that one local floor, for the project's original gate list and its false default for unavailable wires. Lean also proves **19 gates unconditionally** by restricting the ten-vertex test to the nine-vertex theta test and applying its kernel-verified 12-gate lower bound. [Program theorems](src/ProgramFloor.lean) · [Kernel-only local bound](src/KernelFloor.lean) · [Ten-vertex exhaustion](../heawood-129/results.json)

## The 23-gate bound

The full function is determined by 21 minimal positive rows and 37 maximal negative rows. Consider a smallest circuit passing the rows. An output from an initial sequence of gates that has yet to be used by another gate must occur in the remaining circuit. A second way to establish a necessary input is to exhibit a positive row and a negative row distinguished only by that column. The certificate checker tests both conditions. [Prefix checker](prefix.py)

For each branch, the certificate identifies an earlier finite test, an embedding, a replacement for each new signal, and one negative row of the original problem for each negative row of the smaller test. At a positive row, replacing a signal may turn a zero into a one. At a negative row, it may turn a one into a zero. Monotonicity preserves the prescribed output in both cases. All signals must use the same lift for each negative row. Constants among the necessary inputs pay for deleted gates. If the cut sequence has length $d$, there are $c$ such constants, and the smaller test requires $L$ gates, the circuit requires at least $d+c+L$. [Lean proof of signed substitution](src/CutTransfer.lean)

For example, consider a circuit that starts with $v_1\lor v_0$ followed by $v_2\lor v_0$. One ten-vertex test deletes vertices 0, 2, 8 and 10. The second gate becomes zero and remains a required label before that substitution. The first gate becomes the singleton $v_1$. The two cut gates, five deleted labels and the 16-gate local floor give $2+5+16=23$. [Full-graph certificate](prefixes.json.gz)

At each branching point the verifier constructs every pair of available operands, modulo graph symmetries preserving the preceding operations. Repeated operands duplicate an existing signal. A new column that can be replaced by an earlier column or a constant while preserving all row signs would contradict minimality. Every other gate must have a certificate branch. For the full graph, 37 branching prefixes lead to 2,831 verified leaves after two to five gates. Across all 22 root tests the audit checks 324 branching prefixes and 38,099 leaves. The branch enumeration, local exhaustive search decisions and complete census run outside Lean. [Root-by-root decisions](results.json) · [Explicit witnesses](prefixes.json.gz)

## The 26-gate frontier

| Lost edges | Gate lower bound | Remaining symmetry classes | Remaining labeled sets |
|---:|---:|---:|---:|
| 15 | 25 | 2 | 70 |
| 16 | 26 | 5 | 609 |
| 17 | 25 | 8 | 903 |
| 18 | 24 | 5 | 686 |
| 19 | 24 | 3 | 210 |
| 20 | 24 | 1 | 21 |
| 21 | 23 | 1 | 1 |

For each previously open class, the verifier checks actual containment of the positive rows and the available signal masks under the chosen relabeling. It checks equality of the negative rows. The projection charges each surviving edge, a matching of the surviving edges, and each lost-edge endpoint outside the sample. The Fano-plane action then expands every representative and checks its orbit against the complete preceding list. The inventory contains each remaining mask and a SHA-256 digest of each sorted layer. [Transport and orbit checker](transport.py) · [Underlying projection theorem](../heawood-129/src/ProjectedBoundary.lean)

At 15 losses, representatives 32767 and 128895 account for 42 and 28 labeled sets, respectively. Their current gate lower bounds are 26 and 25. Four of the five newly excluded representatives have direct tests with exact minima one gate beyond their budgets. Representative 121855 inherits the 16-gate ten-vertex test. Lean checks the projected budgets for all five. [Five representative tables](src/FifteenScreens.lean) · [Necessary program theorem](src/ProgramFloor.lean)

| Representative | Sample vertices | Budget | Exact minimum | Assignments checked for upper bound |
|---:|---:|---:|---:|---:|
| 114175 | 9 | 12 | 13 | 512 |
| 114686 | 10 | 13 | 14 | 1,024 |
| 126463 | 9 | 12 | 13 | 512 |
| 126719 | 10 | 13 | 14 | 1,024 |

Two exact programs independently exclude each budget. A star circuit attains each displayed minimum. Python and Lean evaluate all four circuits on every assignment to their sampled vertices. [Lower-bound decisions](results.json) · [Circuit descriptions](controls.json) · [Kernel-checked upper bounds](src/SampleControls.lean)

## Reproduction

Run from this directory with Python 3 and a C++17 compiler.

```sh
python3 -B ../heawood-129/verify.py
python3 -B ../heawood-129/frontier.py
python3 -B tables.py
python3 -B check.py
```

The first two commands replay the inherited numerical decisions and the preceding census. The last two verify the concrete Lean tables, rerun both new exhaustive searches for each of the four tests, check all prefix witnesses, and reconstruct the published frontier. The 27-gate construction is evaluated on all 16,384 full-graph assignments. [Numerical replay](check.py)

Use Lean 4.36.0 and the upstream project at revision `048b39bb2c5b2c21da06d44218d16366086a68d9`, with its Mathlib dependencies installed. The proof packet uses its sibling checkpoint directories. The replay authenticates the preceding build and compiles the extension.

```sh
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/heawood-130 --jobs 2
```

[Source manifest](sources.json) · [Kernel audit](kernel.log) · [Verification receipt](verification.json)
