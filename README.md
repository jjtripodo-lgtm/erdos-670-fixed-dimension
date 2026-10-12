# Fixed-dimension Erdős 670: manuscript and Lean formalization

**Research manuscript prepared 12 October 2026.** This repository contains the manuscript and the complete 54-module Lean source closure at source commit `35c67a69e009c9ca27267077608864987b7e2851`. The included sources suffice for the checks and replay described below. This work has not been independently refereed.

The final unconditional theorem, `Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670`, gives for every `n ≥ 68000` an injectively indexed set of `n` points in `EuclideanSpace Real (Fin 458999)`. Every nonzero pair distance is at least one, distances from distinct unordered non-diagonal pairs differ by at least one, and diameter is strictly below `(37/50)n²`. The historical `Erdos488` directory name is only a source identifier; this is the Problem 670 result.

| Read | Location |
| --- | --- |
| Manuscript | [PDF](paper/fixed_dimension_670.pdf), [TeX](paper/fixed_dimension_670.tex), [current validation](verification/manuscript670/CURRENT_VALIDATION.md) |
| Final theorem and proof path | [Lean declaration](lean-fixed670/Erdos488/Geometry/SeparatedDistances/FixedDimension/SourceFixedDimension670.lean), [paper-to-source correspondence](PROOF_CORRESPONDENCE.md) |
| Source identity | [pin](verification/fixed670/SOURCE_PIN.md), [54-module manifest](verification/fixed670/SOURCE_MANIFEST.json) |
| Replay evidence | [status and limits](verification/fixed670/REPLAY_STATUS.md), [machine-readable receipt](verification/fixed670/execution/RECEIPT.json) |
| Prior work and access limits | [prior-art note](PRIOR_ART.md), [citation/access ledger](CITATIONS.md), [citation metadata](CITATION.cff) |

## Read-only verification

From the repository root, with Python 3 installed, run:

```sh
python3 verify_candidate.py
python3 lean-fixed670/verify_sources.py
python3 verification/fixed670/verify_execution.py
python3 verification/fixed670/negative_tests.py
python3 verification/manuscript670/check_manuscript.py > /tmp/fixed670-manuscript-check.json
```

The first four commands check included source identities, dependency locks, receipt claims and deliberately falsified receipt cases. They do not compile Lean. The last command runs supplementary exact arithmetic and LaTeX reference checks, writing outside the repository.

## Fresh Lean replay from public dependencies

Install [elan, the official Lean toolchain manager](https://github.com/leanprover/elan) for your operating system. It selects the exact Lean version in `lean-fixed670/lean-toolchain` (`leanprover/lean4:v4.31.0-rc1`). The following version and checkout checks were tested on the preparation machine; `--fetch` itself was not run there because the public dependency checkouts already existed:

```sh
cd lean-fixed670
elan toolchain install leanprover/lean4:v4.31.0-rc1
lake --version
cd ..
python3 lean-fixed670/prepare_dependencies.py --fetch
python3 lean-fixed670/prepare_dependencies.py
python3 lean-fixed670/verify_sources.py
```

`prepare_dependencies.py --fetch` clones only the nine public Lean dependencies in the committed lockfile, checks out their exact Git commits, and refuses to alter an existing checkout. The read-only form checks all nine HEADs and nonignored dirty states. Do **not** run `lake update`: it can upgrade the lock. Verify that the source checker still passes before building.

For an optional upstream binary-cache route, run `cd lean-fixed670 && lake exe cache get && cd ..` after fetching dependencies. This asks Mathlib's cache tool for prebuilt imports when available. It does not authenticate the origin of any already compiled local `.olean` files. For the no-cache route, omit that command; the first build may compile all needed upstream dependencies. The cache route can download many files; the no-cache route can consume several gigabytes and many hours. Neither route has been tested here as a cold second-machine build. Both require network access for public sources unless their checkouts and artifacts are already present.

In a **fresh extraction with zero project `.olean` files**, run the source-bound replay. Its output path must not exist:

```sh
replay_parent="$(mktemp -d)"
python3 lean-fixed670/replay.py --output "$replay_parent/run"
```

The replay checks the source and lock, the exact nine checkout HEADs, source cleanliness and the zero-project-output condition before its 56 fixed commands. It accepts success only after the six trust-zero axiom prints, exact 54 expected project `.olean` paths, and unchanged source and checkout identities. The recorded run reused pre-existing compiled upstream imports; its receipt states that boundary precisely. [Its status](verification/fixed670/REPLAY_STATUS.md) distinguishes that execution from a full Mathlib rebuild or independent mathematical review.

## Public release and rights

The code and formalization carry the [MIT license](LICENSE); the manuscript source and PDF carry the [separate reserved-rights terms](LICENSE-PAPER). Public availability does not imply independent mathematical review, journal acceptance, or priority clearance. The review and replay limits are stated in the manuscript and [replay status](verification/fixed670/REPLAY_STATUS.md).
