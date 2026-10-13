# Fixed-dimension Erdős 670: manuscript and Lean formalization

**Research manuscript prepared 12 October 2026.** This repository contains the manuscript and the complete 54-module Lean source closure at source commit `35c67a69e009c9ca27267077608864987b7e2851`. The included sources suffice for the checks and replay described below.

Cite the archived manuscript and Lean formalization: version v1.0.0, [DOI: 10.5281/zenodo.23329194](https://doi.org/10.5281/zenodo.23329194).

**[Download paper (PDF)](https://raw.githubusercontent.com/jjtripodo-lgtm/erdos-670-fixed-dimension/main/paper/fixed_dimension_670.pdf)** — direct download if GitHub's PDF preview does not render.

The final unconditional theorem, `Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670`, gives for every `n ≥ 68000` an injectively indexed set of `n` points in `EuclideanSpace Real (Fin 458999)`. Every nonzero pair distance is at least one, distances from distinct unordered non-diagonal pairs differ by at least one, and diameter is strictly below `(37/50)n²`. The historical `Erdos488` directory name is only a source identifier; this is the Problem 670 result.

**Lean verification passed on two machines.** A recorded macOS run and an independent Linux run each rebuilt all 54 project modules from source with zero project `.olean` files and completed the 56-command replay, including six `--trust=0` axiom audits. The final theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. The Linux run also passed a fresh kernel replay of the compiled transitive imports with the pinned Lean checker. The [verification record](verification/fixed670/REPLAY_STATUS.md) gives the exact receipts and upstream binary-cache scope.

| Read | Location |
| --- | --- |
| Manuscript | [PDF](https://raw.githubusercontent.com/jjtripodo-lgtm/erdos-670-fixed-dimension/main/paper/fixed_dimension_670.pdf), [TeX](paper/fixed_dimension_670.tex), [current validation](verification/manuscript670/CURRENT_VALIDATION.md) |
| Final theorem and proof path | [Lean declaration](lean-fixed670/Erdos488/Geometry/SeparatedDistances/FixedDimension/SourceFixedDimension670.lean), [paper-to-source correspondence](PROOF_CORRESPONDENCE.md) |
| Source identity | [pin](verification/fixed670/SOURCE_PIN.md), [54-module manifest](verification/fixed670/SOURCE_MANIFEST.json) |
| Lean verification | [status and scope](verification/fixed670/REPLAY_STATUS.md), [macOS receipt](verification/fixed670/execution/RECEIPT.json), [independent Linux evidence](verification/fixed670/independent-linux-20261012/README.md) |
| Prior work and access limits | [prior-art note](PRIOR_ART.md), [citation/access ledger](CITATIONS.md), [citation metadata](CITATION.cff) |

## Check the included evidence

From the repository root, with Python 3 installed, run:

```sh
python3 verify_candidate.py
python3 lean-fixed670/verify_sources.py
python3 verification/fixed670/verify_execution.py
python3 verification/fixed670/negative_tests.py
python3 verification/fixed670/independent-linux-20261012/validate_bundle.py
python3 verification/manuscript670/check_manuscript.py > /tmp/fixed670-manuscript-check.json
```

These commands check source identities, dependency locks, both recorded Lean runs and their logs, deliberately falsified receipt cases, and supplementary manuscript arithmetic and references. They read the included evidence; to run Lean yourself, follow the build steps below.

## Reproduce the Lean build

Install [elan, the official Lean toolchain manager](https://github.com/leanprover/elan) for your operating system. It selects the exact Lean version in `lean-fixed670/lean-toolchain` (`leanprover/lean4:v4.31.0-rc1`). Dependency fetching was exercised on the independent Linux machine; the earlier macOS run used existing checkouts:

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

For an upstream binary-cache route, run `cd lean-fixed670 && lake exe cache get && cd ..` after fetching dependencies. This asks Mathlib's cache tool for prebuilt imports when available. To attempt an upstream source build, start with dependency checkouts containing zero compiled upstream `.olean` files and omit the cache command; this can consume several gigabytes and many hours. Both recorded runs used upstream compiled imports, as detailed in the [verification record](verification/fixed670/REPLAY_STATUS.md). Network access is needed for public sources unless checkouts and artifacts are already present.

In a **fresh extraction with zero project `.olean` files**, run the source-bound replay. Its output path must not exist:

```sh
replay_parent="$(mktemp -d)"
python3 lean-fixed670/replay.py --output "$replay_parent/run"
```

The replay checks the source and lock, the exact nine checkout HEADs, source cleanliness and the zero-project-output condition before its 56 fixed commands. It accepts success only after the six trust-zero axiom prints, exact 54 expected project `.olean` paths, and unchanged source and checkout identities. The [macOS](verification/fixed670/execution/RECEIPT.json) and [Linux](verification/fixed670/independent-linux-20261012/replay/RECEIPT.json) receipts record the two runs.

After the project build, run the pinned toolchain's checker from `lean-fixed670` to replay the compiled import closure through Lean's kernel:

```sh
cd lean-fixed670
lake env leanchecker --fresh Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFixedDimension670
```

The independent Linux run completed this command. Its [checker receipt](verification/fixed670/independent-linux-20261012/FRESH_KERNEL_REPLAY_RECEIPT.json) records the exact command and terminal result.

## Public release and rights

The code and formalization carry the [MIT license](LICENSE); the manuscript source and PDF carry the [separate reserved-rights terms](LICENSE-PAPER). This AI-assisted research manuscript has not undergone independent mathematical or priority review, and no journal acceptance is claimed. The [Lean build record](verification/fixed670/REPLAY_STATUS.md) states its technical scope.
