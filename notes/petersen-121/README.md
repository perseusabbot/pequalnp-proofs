# Two 16-gate lower bounds for the Petersen graph with one vertex removed

For nine Boolean vertex inputs, the target is true exactly when both endpoints of some edge are true. The project numbers the vertices from 0 through 8. Each gate is an AND, OR or NOT with at most two inputs under the project’s convention. Both theorems rule out programs with at most 15 gates under a specified start.

| Project statement | Required start | Lean theorem |
| --- | --- | --- |
| L-meta-1676 | The first gate computes the OR of inputs 0 and 4. | `Checkpoint121.Compatibility.full` |
| L-meta-3348 | The first gate computes the OR of inputs 4 and 6. The second gate is an OR. | `Checkpoint121.Petersen.full` |

[First-OR theorem](https://github.com/perseusabbot/pequalnp-proofs/blob/petersen-proofs-121/notes/petersen-121/CompatibilityParent.lean) · [Second-OR theorem](https://github.com/perseusabbot/pequalnp-proofs/blob/petersen-proofs-121/notes/petersen-121/PetersenComplete.lean) · [Download the full proof packet](https://github.com/perseusabbot/pequalnp-proofs/raw/refs/heads/petersen-proofs-121/notes/petersen-121/petersen-proofs.zip)

For L-meta-1676, `perseusabbot` supplied the merged reduction. The four child proofs used here are due to `barelyanything`, `loicfontaine-max`, `xxw-keju` and `dsgallups`, in child order. Each public proof is retained in full. [Reduction #4054](https://github.com/open-goat/pequalnp-proofs/pull/4054) · [Child 1](https://github.com/open-goat/pequalnp-proofs/pull/5171) · [Child 2](https://github.com/open-goat/pequalnp-proofs/pull/4608) · [Child 3](https://github.com/open-goat/pequalnp-proofs/pull/4357) · [Child 4](https://github.com/open-goat/pequalnp-proofs/pull/7407)

For L-meta-3348, the second OR may use a raw input or the result of the first OR. The public reduction covers all such choices. Its submitted head passed the upstream project checker. Its last unresolved family required ruling out a 13-gate continuation from each of nine possible input libraries. The proof checks 18,967 states across the nine cases. The signed circuit model and the bit operations for the finite certificates are connected by theorems in Lean. [Reduction #6795 and checker verdict](https://github.com/open-goat/pequalnp-proofs/pull/6795#issuecomment-7138394411)

## Replay

Download `petersen-proofs.zip` from this directory, extract it and run the following commands from the extracted directory. They use Python 3, Git, and the Lean toolchain manager `elan` with `lake` on the path. The upstream revision selects Lean 4.36.0 and the matching Mathlib version. The larger proof checks hundreds of certificate batches and can take several hours.

```sh
sha256sum -c SHA256SUMS --quiet
git clone https://github.com/open-goat/pequalnp-proofs.git project
git -C project checkout 048b39bb2c5b2c21da06d44218d16366086a68d9
(cd project/lean && lake exe cache get && lake build PEqualNP.Defs)
python3 -B research/check121/pairs/replay.py project --build replay --jobs 2 --resume
```

To check one theorem, append `--target CompatibilityParent` or `--target PetersenComplete` to the last command. The replay verifies source hashes, compiles modules in dependency order and checks the final axiom reports. Certified modules can be reused on a later run with the same sources and dependencies. `research/check121/pairs/modules.json` maps every module to its exact input file. Names beginning with `@project/` refer to the pinned checkout's `lean` directory.

The kernel reports for both roots list `propext`, `Classical.choice` and `Quot.sound`. This branch makes the full modular proofs available independently of the upstream project's one-file submission process. The linked pull requests carry the project’s own verdicts. The project sources are licensed under Apache 2.0.
