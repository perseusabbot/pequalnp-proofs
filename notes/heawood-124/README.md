# Six missing edges in short Heawood circuits

The target on 14 input bits is true exactly when the selected vertices contain both endpoints of a Heawood edge. A circuit may share wires and interleave two-input AND and OR gates. Call an AND nested if either operand depends on an earlier AND. Forcing every nested AND output to zero removes at least **six of the 21 minimal positive edge inputs** from any correct circuit with at most 26 gates. Checkpoint 123 established a lower bound of four.

| Maximum number of gates | Minimum number of lost edges |
| ---: | ---: |
| 26 | 6 |
| 25 | 6 |
| 24 | 7 |
| 23 | 8 |
| 22 | 9 |

The proof covers arbitrary output wires, repeated operands and the evaluator’s default zero for unavailable operands. It also specializes to all 65 pairs of opening gates in the project’s packed evaluator and all four operation choices. Whether a correct 26-gate circuit exists remains open.

## Why four or five losses are impossible

Write H for the graph of surviving edges and j for the number of distinct ordinary products represented in the pruned output. A regular signal is the OR of at most one input, or the OR of a subset of the neighbors of one vertex in H. A conjunction of regular signals cannot restore two distinct missing edge inputs without accepting an input on which the graph predicate is false. For each pair of missing edges the proof supplies a false input that hits every regular signal hitting both edge inputs. The same false input works for every conjunction built from those signals. The independent replay checks all 210 unordered pairs.

The count k includes each bottom OR with nonregular support, each ordinary AND with a product absent from the pruned output, each OR with exactly one AND-free operand, and every nested AND. The rectangle bound on the retained graph, together with the costs of producing and joining the products, gives

`|H| + j + k ≤ number of gates` and `|H| ≤ 3j`.

Consider the inputs on which pruning gives zero. Every retained ordinary product vanishes there. To model the remaining computation, the proof allows arbitrary regular signals as inputs and free unions of already produced impure signals. It represents the output as an OR of conjunctions of regular signals. Two fresh formal variables per counted gate allow each occurrence to stand for a different regular signal, including repeated use of a previous one. Lean proves the representation uniformly on the entire restricted input domain.

| Counted gates k | Maximum number of conjunctions after absorption, with a nested gate |
| ---: | ---: |
| 1 | 0 |
| 2 | 1 |
| 3 | 2 |
| 4 | 4 |

If four edges disappear, 17 survive. At least six products are needed, leaving at most three counted gates in a 26-gate circuit. Those gates can restore at most two edges. If five disappear, 16 survive, again needing six products. The remaining four gates can restore at most four edges. The same accounting gives `4|H| ≤ 3(number of gates − 5)` for every correct circuit of at most 26 gates.

## The six-edge case

Exactly six losses require at least 25 gates. At 25 gates there are five surviving products and five counted gates. At 26 gates the surviving product count is five or six.

With five products the fifteen surviving edges are the full set of edges incident to five centers. Of the 2,002 choices of five vertices, 56 give fifteen distinct incident edges, each with a different omission. Lean checks the resulting six-edge graphs. In 42 cases the omitted edges are two three-edge stars that share one leaf. In 14 cases they are three disjoint paths of length two. These are necessary conditions. Realizing any of the 56 patterns with 25 gates and the six-product case at 26 gates remain open.

## Controls

The independent program constructs 635 circuits with 28 gates. For each of five valid staged openings it takes a nonempty subset of the seven star products, joins that subset, and inserts an AND of the result with itself. The original circuit computes the predicate. After pruning it loses precisely the edges incident to the selected star centers. The verifier compares both outputs on all 16,384 vertex assignments and on the posted packed inputs.

| Lost edges | 3 | 6 | 9 | 12 | 15 | 18 | 21 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Controls | 35 | 105 | 175 | 175 | 105 | 35 | 5 |

## Reproduction

The src directory contains all 35 Lean modules in the manifest. Use the pinned Lean 4.36.0 project checkout. From this notes directory run the following commands.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --packet . --graph modules.json --build /tmp/heawood-124 --target FiveCenters --jobs 1
python3 -B reproduce.py --stages src/HeawoodStages.lean --prefixes prefixes.json --statement statement.txt
```

The principal Lean theorems are `Checkpoint124.Heawood.sixLost`, `postedSixLost`, `smallerCircuits` and `sixAtTwentyFive`. The final theorem audits use only propositional extensionality, classical choice and quotient soundness. The independent shape check uses Boolean truth tables on eight formal variables and counts their minimal true assignments.
