# Checkpoint 138

On the desk’s 21 by 21 matrix, any cover of all 336 zeros by at most 14 all-zero rectangles needs **at least three rectangles that cannot fit inside a legal 6 by 6 rectangle**. Call these rectangles exceptional. The unrestricted minimum is still between 13 and 15 inclusive. Jonathan Chassot proved the lower bound of 13, and DPS0340 supplied the 15-rectangle cover. The desk still lists both existence questions and their opposites. [Checked lower bound](https://github.com/open-goat/pequalnp-proofs/pull/21189) · [Checked upper bound](https://github.com/open-goat/pequalnp-proofs/pull/13338) · [Desk record](desk.json)

Two further results narrow the search. If a cover of size at most 14 has exactly three exceptions, **at most one of them can fit inside an area-16 maximal rectangle**. And if all rectangles must fit inside legal 6 by 6 rectangles, **fifteen rectangles cover at most 334 zeros**, a bound attained by the published example. Sixteen suffice for all 336. [Three-exception decisions](triples.json) · [One-hole decisions](near.json) · [Earlier full-cover result](../checkpoint-137/README.md)

## A test using four cells

For any set of cells, at most four of its own cells determine exactly which of the 168 legal 6 by 6 rectangles contain the entire set. Four are sometimes necessary. In column 0 the cells in rows 2, 5, 6 and 7 are all zero. Every three fit in a legal 6 by 6 rectangle, and the four together do not. The dual result also holds. The common cells of any family of maximum rectangles equal the common cells of at most four members. [Lean theorems and sharp example](src/FourCells.lean)

This gives an exact replacement test in a complete cover. Remove one rectangle and collect the zero cells it alone covered. At most four of those cells determine **every** maximum rectangle that can replace it. In a cover chosen to minimize the number of exceptions, each exception therefore has a witness of at most four private cells that rules out replacement. [Lean replacement theorem](src/PrivateCells.lean)

The proof minimizes a determining subset. Five indispensable cells would give five maximum rectangles, each excluding its corresponding cell and containing the other four. The checked symmetries send the first rectangle to a fixed one. The distinguished outside cell then has three representative positions. In each position Lean verifies the restricted incidence masks and rules out the remaining four-by-four off-diagonal pattern. The proof also applies to the transposed relation. [Finite-set argument](src/Compression.lean) · [Local tables and symmetry words](src/LocalData.lean)

A separate enumeration classifies the minimal cell obstructions whose row and column labels together form a legal rectangle. It finds 325,920 triples and 1,053,360 quadruples, in 20 symmetry classes. At the level of required row and column labels there are three kinds of minimal obstruction, up to symmetry and transpose. They have 420, 5,040 and 20,160 instances. The geometry file gives representatives. It also records the partition of the 168 rectangles into three classes of 56 by parity of row overlap. Every triple covering all 16 zeros of a row or column uses one rectangle from each class. [Enumeration](obstructions.py) · [Representatives](geometry.json)

## Degree balance and the search

Write \(d_p\) for the number of selected maximum rectangles using point \(p\) as a row, and \(d_\ell\) for the corresponding column count for line \(\ell\). Incidence in the projective plane means a **one** in the matrix. For any family of \(m\) distinct maximum rectangles,

\[
2d_p+\sum_{\ell\ni p} d_\ell=2m,\qquad
2d_\ell+\sum_{p\in\ell}d_p=2m.
\]

Each rectangle contributes two to each identity. For example, a rectangle containing row \(p\) uses none of its incident lines, and a rectangle omitting \(p\) uses exactly two. Lean checks the individual identities on the posted board and sums them over an arbitrary family. [Formal proof](src/Degrees.lean)

The parities of the 21 row degrees must therefore meet each line evenly. Binary elimination gives 2,048 possible parity patterns. For each pattern the solver starts at the least permitted row degrees, adds units of two until the row-degree sum reaches \(6m\), and derives every column degree from the displayed identity. During search it discards profiles only when they violate a necessary count. A label at its maximum possible degree permits no further selection through that label. Cells with a single remaining rectangle force that selection. For a row or column that must finish at degree three, the solver can enumerate all feasible covering triples. Otherwise it branches over the choices at an uncovered cell. [Degree and cover search](degree_search.cpp)

For two exceptions, extend each to an inclusion-maximal rectangle and extend every other rectangle to 6 by 6. Coincident exceptional extensions reduce to the earlier one-exception case. There are 25,067 nonempty exceptional maximal rectangles and 314,164,711 unordered pairs of distinct ones. The full board group reduces the search to 2,487 representative cases using the earlier convention that sometimes retains both orders within one shape. Every case excludes twelve further maximum rectangles, in 139,466,144 states. A smaller family can be padded with unused maximum rectangles. A previous solver using a different search algorithm separately excluded 261 of these cases, including all 62 involving a 4 by 4 maximal rectangle. [All pair decisions](pairs.json) · [Previous solver decisions](reference.json)

For three exceptions, the area-16 maximal rectangles consist of 42 stars of shape 1 by 16 or 16 by 1 and 105 rectangles of shape 4 by 4. Mark two of these 147 rectangles and allow any of the 25,067 exceptional maximal rectangles as the distinct third. The stabilizers of nine marked-pair representatives yield 3,394 cases covering all 267,935,185 unordered physical triples with at least two small rectangles. None admits a completion with eleven maximum rectangles. If two proposed maximal extensions coincide, the two-exception result applies. [Enumeration and lifting inputs](triples.py) · [Decisions](triples.json)

## Why fifteen maximum rectangles miss at least two cells

The fifteen-rectangle witness misses precisely the zeros at row 8, column 16 and row 10, column 16, using zero-based indices. Lean checks the 334 covered cells directly on the posted matrix. [Witness](src/NearWitness.lean)

Suppose a family misses exactly one zero. Move that hole to row 0, column 1. If necessary, pad the family to size 15 using rectangles avoiding the hole. A full row or column needs at least three rectangles. Three maximum rectangles through one label cover all 16 zeros or at most 14, so each of the two labels bordering the hole needs at least four. If a different label has degree three, its triple is one of 3,840 possibilities. The hole stabilizer has order 720 and partitions these into eight cases. The earlier solver excludes all eight in 228,062,995 states, even when the selected rectangles are allowed to hit the prefilled hole. [Case inventory and decisions](near.json)

Otherwise every row and column has degree at least four. There are exactly six surplus incidences on each side. Subtracting four from each degree gives nonnegative weights \(r_p,c_\ell\), with \(\sum_{p\in\ell}r_p+2c_\ell=2\). Two distinct points lie on a common line. If any point had surplus at least two, all others would have zero, contradicting total surplus six and the line bound. Thus all surpluses are zero or one, and no heavy point is incident with a heavy line. The six heavy rows and six heavy columns form one legal maximum rectangle. This rectangle describes the degree counts and need not have been selected. [Lean proof](src/Degrees.lean)

Under the hole stabilizer the surplus rectangle has three possible positions, with orbit sizes 90, 60 and 18. The search excludes all three in 2,866,691 states. A separate run without the orbit reduction enumerates all 168 possible degree profiles and reaches the same conclusion. The earlier size-15 full-cover exclusion and the checked 334-cell construction then give the exact maximum. [Three-case search](near.json) · [All-profile search](whole.json)

## Reproduction and continuation

The numerical programs use Python 3 and a C++20 compiler. Run the following from this directory in a checkout containing the preceding checkpoints. The reference replay without the sample switch checks all 261 decisions from the previous algorithm.

~~~sh
python3 -B replay.py pairs --jobs 3
python3 -B replay.py near --jobs 3
python3 -B replay.py whole
python3 -B triples.py --jobs 2
python3 -B reference.py --sample --jobs 2
python3 -B obstructions.py
python3 -B proofs.py /path/to/pinned/upstream --build /tmp/checkpoint138-lean --jobs 2
~~~

The proof replay expects upstream commit 501dda8586110abcaebe0ea32060309d020bb2ee, Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 and Lean 4.36.0. It regenerates the normalization tables and compares the board and witnesses before auditing the new declarations. The coverage exclusions use exhaustive numerical searches. The compression, sharpness, replacement, degree and surplus theorems and the positive witness are kernel-checked. [Verification receipt](verification.json)

The ongoing size-13 search permits three exceptional rectangles of any shape and ten maximum rectangles. The journal saves completed first-pair cases and checks its input and solver signature on restart. The search tests the returned rectangles directly against the posted matrix if it finds a cover. The saved journals also continue the earlier one-hole and Heawood searches. [Size-13 driver](frontier.py) · [Earlier search drivers](../checkpoint-136/README.md)

~~~sh
python3 -B frontier.py /path/to/three-at-13 --jobs 1
~~~
