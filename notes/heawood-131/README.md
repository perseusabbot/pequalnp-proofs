# Heawood circuit bounds at Checkpoint 131

The full Heawood edge function requires **at least 24 and at most 27** binary monotone AND or OR gates. The lower bound allows arbitrary fanout, depth, and opening gates. A 24-gate circuit would have to open with OR and lose all 21 edge inputs under the pruning defined below. The project's question about a 26-gate circuit with one of its 65 prescribed openings remains open. [Previous checkpoint](../heawood-130/README.md) · [Numerical results](results.json)

At most 246 labeled loss sets in six graph-symmetry classes can still occur at 26 gates. Checkpoint 130 left 2,500 sets in 25 classes. An edge input sets exactly its two endpoints to true. It is lost when the circuit stops accepting it after every AND with an earlier AND among its input ancestors is forced to zero. The minimum loss count at this budget is now **at least 18**. [Complete class inventory](frontier.json)

## Why 23 gates are insufficient

Remove vertex 6 and its incident edges. The remaining 13-vertex problem has 13 singleton inputs, 18 required edge rows, and 30 maximal independent rows that must be rejected. An exhaustive signed search excluded circuits through 21 gates. It expanded 863,353 states. [Finite row data and embeddings](src/DeletionData.lean) · [Search results](results.json)

Choose a bottom gate on two distinct vertices in a smallest full circuit. Cutting it out saves one gate and provides its value to the rest of the circuit as an input. Call its operands $x$ and $y$. The remaining circuit must still read $x$. For AND, hold $y$ false, and for OR, hold $y$ true. There is a positive row and a negative row differing only at $x$ with that value of $y$. The cut gate has the same value on both rows. Lean checks these witnesses for every distinct ordered pair. [Witness family](src/DeletionData.lean)

Relabel the graph so that $x$ is the deleted vertex, then set it to false. The fresh gate input becomes zero for AND or the surviving operand $y$ for OR. The old input $x$ becomes zero and occurs in the remaining circuit. Pruning that label saves at least one more gate, including in a circuit with shared wires. A full circuit of size $g$ therefore gives a circuit of size at most $g-2$ on the 13-vertex test. Its 22-gate lower bound gives $g\ge24$. If the bottom gate is AND, its fresh output and $x$ are two distinct, used constant labels, giving $g\ge25$. A minimum circuit can omit unused gates and simplify repeated operands. [Lean deletion and bottom-AND theorems](src/VertexDeletion.lean)

A second calculation works directly on the full graph's 21 edge rows and 37 maximal independent rows. One possible initial support contains all 14 vertices. The program examined 75,861 states and exhausted that support at 23 gates. Lean checks the row signs, the exact 14 input columns, and the implication from a finite row lower bound to the project's original instruction-list representation. Every posted witness therefore needs at least 22 operations after its prescribed opening pair. [Full-row bridge](src/FullRowFloor.lean) · [Full search and dependencies](projections.json)

## How the search excludes a circuit

The search follows the gates that feed the output. It chooses the primary inputs used by that circuit and tries both operations for each pair of distinct live wires. After a gate, each operand stays live if it will be used again. Every other live wire stays, and the fresh wire is added. This covers every order of a minimum circuit. With $k$ gates left, at most $k+1$ distinct live labels can occur in one output. Every positive-negative pair must still be separated by a live column. A fresh column that an earlier signal can replace on all root rows would shorten a minimum circuit. [Exhaustive implementation](signed_search.cpp)

Each smaller test has a known lower bound $L$. Its positive rows occur among the root's positives. For each smaller negative row the checker verifies a single negative extension in the root, shared by all signals. A replacement may increase a signal on the selected positives and decrease it on the selected negatives. Monotonicity preserves the required output. A gate can reuse a local input, a constant, or a previously translated wire whenever it satisfies those inequalities. Otherwise rebuilding it costs at most one local gate. Each rebuilt gate is shared by all its later uses. [Embedding and lift checker](geometry131.py) · [Lean gate translation](src/TranslatedGate.lean)

Suppose $S$ prefix gates have been saved and $c$ distinct labels used in the remaining circuit translate to constants. A root circuit of size $g$ would give a local circuit of size at most $g-S-c$. The search discards the branch whenever $L+S+c>g$. Its memo key includes the remaining budget, the live column set, and the current allowance for every local test. Once a memo table is full, the search can revisit uncached states. It enumerates through completion. [Lean cost and shared-prefix composition](src/RebuiltPrefix.lean) · [Constant-pruning theorem](../heawood-130/src/ConstantPruning.lean)

## The 26-gate cases

| Lost edges | Lower bound for the class layer | Remaining symmetry classes | Remaining labeled sets |
|---:|---:|---:|---:|
| 15 | 27 | 0 | 0 |
| 16 | 27 | 0 | 0 |
| 17 | 27 | 0 | 0 |
| 18 | 25 | 1 | 14 |
| 19 | 25 | 3 | 210 |
| 20 | 25 | 1 | 21 |
| 21 | 24 | 1 | 1 |

For the last two 15-loss representatives, mask 32767 would leave at most 17 gates on its 11-vertex test and mask 128895 would leave at most 18 on its 12-vertex test. The searches give respective local lower bounds of 18 and 19. At 17 losses, the last representative, mask 131071, would leave at most 20 gates after accounting for four retained edges and a matching of size two. Its 13-vertex test requires at least 21. Lean checks the boundary budgets for these cases. The census transports established lower bounds through the 336 automorphisms, verifies the signal and row inclusions, and reconstructs every previously open labeled mask. [Boundary theorems](src/SurvivingScreens.lean) · [Census checker](inventory.py)

The sole surviving 18-loss class has representative 262143. Its three retained edges are the star around one vertex. The 14 choices of center account for the 14 labeled cases. Its projected 13-vertex test permits the disjunctions of that vertex's neighbors as free inputs. The original 26-gate budget allows 22 gates on this test. [Class details](frontier.json)

## Verification and reproduction

Two independent searches first excluded 15 gates on the ten-vertex test for mask 128895. They expanded 17,206,410 last-use states and 15,701,748 availability states. An explicit circuit attains 16 gates. The signed checker then completed 14 decisions across 25,352,451 expanded states. Its answers on 66 small instances agree with an independent enumeration of all 18 nonconstant, three-variable monotone truth tables. Four damaged projection descriptions are rejected. Three explicit circuits are checked on 7,168 local assignments, including an 18-gate upper bound for mask 32767. The inherited 27-gate construction is evaluated on all 16,384 full assignments. [Controls](controls.json) · [Kernel-checked local upper bounds](src/LocalStars.lean) · [Verification receipt](verification.json)

The numerical exhaustions and the symmetry census run outside Lean. The kernel proves the two-gate deletion, the extra saving for a bottom AND, the signed gate and suffix cost rules, and the finite-row bridges. Applying the deletion theorem to the externally computed 22-gate lower bound gives 24. The inherited unconditional full-graph kernel lower bound is 19. [Kernel audit](kernel.log) · [Previous unconditional result](../heawood-130/src/KernelFloor.lean)

Run the following from this directory with Python 3 and a C++17 compiler. The default checker reruns both independent ten-vertex searches. The optional flag `--use-basis-receipt` reuses their recorded decision while replaying every signed decision, control, and symmetry class. [Search driver](check.py)

```sh
python3 -B ../heawood-130/check.py
python3 -B row_tables.py
python3 -B check.py --jobs 2
```

The Lean replay uses version 4.36.0 and upstream revision `048b39bb2c5b2c21da06d44218d16366086a68d9` with Mathlib installed. It authenticates the sibling checkpoint dependencies before compiling this extension. [Source manifest](sources.json)

```sh
python3 -B replay.py /path/to/pequalnp-proofs --build /tmp/heawood-131 --jobs 2
```
