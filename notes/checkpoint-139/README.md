# Checkpoint 139

**Any cover of the 336 zeros on the desk’s 21 by 21 board with at most 13 rectangles needs at least four rectangles that cannot fit inside a legal 6 by 6 rectangle.** Call such a rectangle exceptional. If there are exactly four exceptions, none can fit inside a maximal rectangle of area 16. The same area restriction holds for a cover of size at most 14 with exactly three exceptions. [Search results](results.json) · [Previous two-exception result](../checkpoint-138/README.md)

The unrestricted minimum remains between 13 and 15 inclusive. Jonathan Chassot proved the lower bound of 13, and DPS0340 exhibited a cover of size 15. The desk still lists the existence and impossibility questions at sizes 13 and 14. [Lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [Upper bound](https://github.com/open-goat/pequalnp-proofs/pull/13338) · [Desk snapshot](desk.json)

## The excluded covers

Every extendible rectangle can be enlarged to one of the 168 legal maximum rectangles. Every exception can be enlarged to one of the other 25,067 inclusion-maximal rectangles. The smallest maximal rectangles cover 16 cells. They consist of 42 rectangles of shape 1 by 16 or 16 by 1, and 105 of shape 4 by 4. Every other exceptional maximal rectangle covers between 24 and 28 cells.

| Total budget | Exceptional maximal rectangles | Further maximum rectangles | Unordered physical choices of exceptions | Representative cases excluded |
|---|---|---:|---:|---:|
| 13 | Three of any shape | 10 | 2,624,846,160,405 | 22,298,616 |
| 14 | Three, at least one of area 16 | 11 | 45,910,073,965 | 267,688 |
| 13 | Four, at least two of area 16 | 9 | 3,344,819,934,680 | 28,955,911 |
| 13 | Four, exactly one of area 16 | 9 | 379,103,604,706,680 | 3,214,846,934 |

Each row of the table covers all indicated choices. The symmetry acts on the board and marks the first rectangles. The rest of a proposed cover can be completely asymmetric. At a fixed marked pair, the program takes every orbit of eligible third rectangles. For four exceptions it also takes every orbit of eligible fourth rectangles under the stabilizer of the first three. The recorded multiplicities recover each physical total. Some equal-shape markings produce more than one representative of the same unordered orbit. [Input construction](inventory.py) · [Orbit search](scan.cpp)

The conclusions apply to the original rectangles, including nonmaximal ones. If an exceptional rectangle fits in an area-16 maximal rectangle, choose that extension. Coincident exceptional extensions reduce the number of exceptions and invoke an earlier exclusion. After discarding duplicate maximum rectangles, unused maximum rectangles can pad the family to the indicated budget.

## Why the search is smaller

For each point or line \(v\), let \(L_v\) be the minimum number of maximum rectangles needed to cover its zeros still exposed after placing the exceptions. This number is at most three. The local table checks all single rectangles and pairs through \(v\), together with a triple that covers the whole label. [Local tables](board.hpp)

For \(m\) selected maximum rectangles, let \(d_p,d_\ell\) be their row and column degrees. They satisfy \(2d_p+\sum_{\ell\ni p}d_\ell=2m\) and the dual identity. Each side has total degree \(6m\). From the known lower bounds \(L_v\), the solver computes the available surplus on each side. The points with odd degree meet each line evenly. A 10-bit binary syndrome indexes exactly the parity corrections attainable with the remaining surplus. After choosing a correction on one side, the solver distributes the remaining degrees in steps of two. The incidence identity determines all degrees on the opposite side. [Earlier formal identity](../checkpoint-138/src/Degrees.lean) · [Degree enumeration](profiles.hpp)

For every resulting degree assignment, the completion search enforces those counts while covering all exposed cells. A remaining capacity of one or two at a point or line lets it branch on whole local completions. Otherwise it uses an uncovered cell or a label with a positive remaining count. Each affirmative control is checked directly against all required cells. [Completion search](complete.hpp) · [Controls](controls.cpp)

Of the 22,298,616 three-exception cases at size 13, only 178,785 admit even one integral degree assignment. Those cases generate 289,659 assignments. The previous solver reconstructed the degree counts and excluded all 521,201 residuals that passed the local, domination and parity tests. An earlier algorithm using no joint degree profiles separately excluded a systematic sample of 3,750 residuals. For the four-exception result, this degree-free algorithm also checks every representative that admits an integral assignment. [Three-exception cross-check](reference.json) · [Four-exception cross-check](four-reference.json)

## Rows and columns used at most twice

Call a row or column *light* when at most two selected maximum rectangles use it. Nine maximum rectangles have at least **ten** light labels. Ten maximum rectangles have at least **eight**. Both bounds are sharp. Each light label has at least five zeros requiring another rectangle, since two maximum rectangles through it cover at most eleven of its sixteen zeros. [Lean bounds](src/Nine.lean) · [Local bound](src/Domination.lean) · [Sharp witnesses](src/Extremal.lean)

For at most ten maximum rectangles, the light points and lines dominate the incidence graph of the plane. If a point and all five incident lines had degree at least three, their weighted degree sum would be at least 21, exceeding twice the budget. The same holds at every line. A set of \(k\) points meets at most \(4k+1\) lines, giving the lower bound of eight light labels. At equality the four light rows and four light columns form a maximal 4 by 4 zero rectangle.

With at most nine maximum rectangles, eight or nine light labels would force one side to have four light labels and the opposite side at most five. Four points meeting at least sixteen lines must be collinear. At least sixteen points outside their common line then have degree at least three. Degree balance and the fact that an incident point and line cannot appear together in a zero rectangle force degree three at every point outside that line and at its fifth point. Another line through that fifth point has odd degree sum 15, contradicting degree balance. The dual argument treats four light columns. Lean checks this argument for arbitrary families. [Proof](src/Nine.lean)

**In a full size-13 cover with exactly four exceptions, the other nine rectangles, even after enlargement to legal 6 by 6 rectangles, must leave at least thirteen light row and column labels in total.** Nine maximum rectangles with at most eleven light labels cover at most 215 cells. This bound is sharp. Four exceptional rectangles can cover at most 112 more cells, so the nine would have to cover at least 224.

The calculation enumerates 57 possible light-set representatives up to eleven labels. Only two support families of nine maximum rectangles. With ten light labels, the five light rows lie on a line and the five light columns pass through a point outside that line. All nine rectangles contain the corresponding zero. There are 20 families at each of its 336 possible positions, and each covers 181 cells. With eleven light labels, the one surviving class has 5,040 positions and 191 families at each. Their coverage ranges from 204 to 215 cells. The packet records the entire coverage distribution and witnesses. [Light-set enumeration](patterns.py) · [Family enumeration](patterns.cpp) · [Results](results.json)

For exactly twelve light labels, there are 338 further light-set representatives. Only four support any family of nine maximum rectangles. Just one supports families covering at least 224 cells. At each of its 6,720 possible light-set positions, 54 families cover 224 and 72 cover 225. For each of the 126 families at the representative position, the table lists five uncovered zeros. Every pair has a cross-entry equal to one, so no legal rectangle can contain both. Covering those five cells requires at least five further rectangles. Symmetry carries these certificates to all 846,720 families meeting the area threshold. [Twelve-label results](twelve.json) · [Five-cell witnesses](twelve-witnesses.tsv) · [Certificate checker](twelve.py)

A second checker reads the incidence matrix straight from the upstream Lean source and reconstructs every maximal rectangle by intersecting its rows. It checks each of the 25,235 maximal rectangles against each of the 126 witnesses. None covers two marked cells. It also finds that any single exception adds at most 24 cells to each of these nine-rectangle families, giving independent upper bounds of 320 and 321 for the two coverage sizes after four exceptions. [Direct matrix check](direct_cells.py) · [Counts](direct-cells.json)

Each witness row starts with the nine zero-based indices in the sorted inventory of maximum rectangles. The final five entries encode cells as 21 times the zero-based row index plus the column index.

## Reproduction

Run these commands from this directory with Python 3 and a C++20 compiler. The residual file connects the first search to its independent replay.

~~~sh
python3 -B check.py three --jobs 3 --residuals /tmp/pnp139-residuals
python3 -B reference.py /tmp/pnp139-residuals --jobs 3
python3 -B check.py three-small --jobs 2
python3 -B check.py four-two-small --jobs 2
python3 -B check.py four-one-small --jobs 3
python3 -B four_reference.py
python3 -B check.py lights
python3 -B twelve.py
python3 -B direct_cells.py /path/to/pinned/upstream/lean/PEqualNP/Outside/L_meta_9338.lean twelve-witnesses.tsv
python3 -B check.py controls
python3 -B proofs.py /path/to/pinned/upstream --build /tmp/pnp139-lean --jobs 2
~~~

The Lean replay rebuilds three earlier source modules and three new ones using Lean 4.36.0 and the pins in the verification receipt. The universal light-label bounds, the local eleven-cell limit, and the explicit witness counts are kernel-checked. The cover exclusions and coverage histograms use exhaustive numerical searches. [Verification](verification.json)

The open size-13 search now permits four exceptional rectangles of areas 24 through 28. Its journal records each completed marked pair and validates any candidate on the original board. The publication includes saved journals for this search, the earlier three-exception and two-exception cross-checks, the one-hole search around the 334-cell size-14 example, and the reduced 22-gate Heawood search. [Remaining four-exception search](large.py) · [Saved work](resume)

~~~sh
python3 -B large.py /path/to/writable/four-large
~~~
