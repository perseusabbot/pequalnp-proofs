# What a 26-gate Heawood circuit loses when nested ANDs are cut

The edge predicate on the Heawood graph has fourteen inputs. It accepts when both endpoints of some edge are selected. Project gap L-meta-3541 asks for a monotone circuit using at most 26 gates under one of 65 prescribed opening wire pairs. A solution remains open.

An AND is nested when one of its inputs depends on an earlier AND, possibly through OR gates. Set the output of every nested AND to zero, leaving all other gates and wires in place. **A correct circuit with at most 26 gates must then miss at least four of the graph’s 21 positive edge assignments. With at most 24 gates it must miss at least five.** The first bound applies directly to the posted packed evaluator, including shared wires, interleaved operations, and the zero default for unavailable input indices.

## Why three missing edges are impossible

At three missing edges, Checkpoint 122 showed that the edges meet at a vertex and the pruned circuit contains six surviving ordinary products. The original circuit would have exactly one nested AND and twelve ORs joining wires free of AND ancestors.

Set all inputs outside that vertex and its three neighbors to zero. Every surviving ordinary product vanishes. Each pure wire now depends on at most one of the four remaining inputs. To prove the latter claim, add the missing three-leaf star back to the six products. Any two of its leaves can supply the pair used to build their triple. The resulting optimal three-stage library accounts for every original bottom OR.

An ordinary AND that remains nonzero can introduce at most two of the restricted inputs into wires with AND ancestors. A mixed OR or a nested AND can introduce at most one. The gate counts from the three-edge case allow at most three inputs to affect the output. The required predicate on the star depends on all four. Switching either endpoint of a selected edge to zero demonstrates the dependence.

## The boundary at four lost edges

Lean gives six possible gate-count profiles for a circuit with at most 26 gates that loses exactly four edges. An ordinary AND has two inputs free of AND ancestors. A mixed OR has exactly one such input. A bottom OR has two, and a top OR has none.

| Surviving products | Bottom ORs | Top ORs | Ordinary ANDs plus mixed ORs | Nested ANDs | Total gates |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 11 | 6 | 7 | 1 | 25 |
| 6 | 12 | 6 | 7 | 1 | 26 |
| 6 | 11 | 7 | 7 | 1 | 26 |
| 6 | 11 | 6 | 8 | 1 | 26 |
| 6 | 11 | 6 | 7 | 2 | 26 |
| 7 | 10 | 7 | 8 | 1 | 26 |

When six products survive, six vertices cover the seventeen surviving edges. Lean checks that the six-center condition admits exactly **294 distinct four-edge omissions**. Every two-nested-AND circuit at this boundary falls in that family. The seven-product case remains separate. Circuit realization within the 294 cases remains open.

| Shape of the four missing edges | Edge sets |
| --- | ---: |
| Three edges at one vertex and a fourth edge disjoint from that star | 168 |
| Three edges at one vertex and a fourth touching a leaf | 84 |
| Two vertex-disjoint paths of two edges each | 42 |

The census uses the edge order in the project’s Heawood graph definition. An independent enumeration first tests all 3,003 six-vertex center sets, then tests all 5,985 four-edge omissions by branching on uncovered edges. It finds exactly one six-vertex cover for each of the 294 accepted omissions. The numbered edges and cover vertices for every case are in [census.json](census.json).

The 294 sets form exactly **three classes under vertex relabellings that preserve adjacency**, one for each row of the shape table. Representatives in zero-based edge order are `[0,1,2,4]`, `[0,1,2,3]`, and `[0,1,13,14]`, respectively. To obtain the full group, enumerate the 5,040 permutations of one side of the connected bipartite graph. Exactly 168 preserve the seven neighborhoods on the other side. A symmetry exchanging the two sides gives the other 168 automorphisms. The program checks every map against the graph and records an explicit relabelling for each of the 294 sets. Lean checks those witnesses using two verified graph automorphisms. [Orbit certificates](symmetry.json)

Fixing the two opening gates changes the count. For each of the 65 published wire pairs, the enumeration retains only automorphisms preserving each gate’s two operands as an unordered pair and fixing the wire produced by the first gate. Depending on the opening, the 294 sets split into 28 to 294 classes. The 65 counts sum to 9,255 for any one choice of the two operation flags. Direct orbit enumeration and independent fixed-point counts agree for each opening. [Counts by opening](symmetry.json)

## Positive controls

For each of the five previously verified 27-gate staged openings and each of its seven star centers, insert an AND that reads the chosen product twice. All 35 circuits have 28 gates, retain the prescribed first two operations, and compute the posted target. Cutting their sole nested AND loses precisely that center’s three edges. Lean verifies the packed computation. The independent evaluator also checks the full and pruned outputs on all 16,384 assignments per circuit. [Control results](controls.json)

## Reproduction

The src directory contains all 31 Lean source modules in the manifest. Use the pinned Lean 4.36.0 toolchain and project checkout. From this notes directory, run the following commands.

```sh
git clone https://github.com/open-goat/pequalnp-proofs.git /tmp/heawood-project
git -C /tmp/heawood-project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd /tmp/heawood-project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B replay.py /tmp/heawood-project --packet . --graph modules.json --build /tmp/heawood-123 --target OrbitClasses --target StarControls --jobs 1
python3 -B census.py --stages src/HeawoodStages.lean
python3 -B controls.py --stages src/HeawoodStages.lean --prefixes prefixes.json --statement statement.txt
python3 -B symmetry.py --stages src/HeawoodStages.lean --statement statement.txt
```

The principal theorems are `Checkpoint123.Heawood.postedFourLost`, `Checkpoint123.Heawood.fourProfiles`, `Checkpoint123.Census.exactOptionCount`, `Checkpoint123.Census.twoCutMasks`, `Checkpoint123.Census.fiveBelow25`, and `Checkpoint123.Symmetry.threeRepresentatives`. [Prior lower bound](https://github.com/perseusabbot/pequalnp-proofs/tree/f5a43646b4df7420bac25187f61a54a804c228f9/notes/heawood-122)
