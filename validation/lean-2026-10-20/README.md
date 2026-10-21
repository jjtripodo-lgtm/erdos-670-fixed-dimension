# Reproducible Lean sources for the later separated-distance results

This additive package supplies the actual proof sources and their complete local
import closures for the newer formal results cited in the 20 October 2026 paper.
It leaves the paper, earlier proof package and historical evidence unchanged.

Two separate Lake projects are intentional: their local module names overlap.

| Project | Source target | Scope |
|---|---|---|
| `r29` | `R29MinimalBridge` | Unbounded sizes in dimension 29, indexed endpoint, finite-set translation, exact fixed-dimensional conjecture negation |
| `epsilon` | `FullFamily` | Arbitrary-epsilon and uniform-dimension families, under their explicit numerical thresholds |

The R29 result is an **unbounded subsequence**, not an all-size theorem. The
paper's every-n >= 400,000 result using Dusart remains a written proof; this
package neither removes it nor claims to formalize it. Read the exact Lean
declarations for hypotheses, dimensions, strictness and quantifiers.

## Reproduce

Install Lean **4.33.1** using the official Lean/elan distribution. Each project
pins Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474` and includes the
complete dependency lockfile. From this directory:

```sh
python3 verify_sources.py
(cd r29 && lake exe cache get && LEAN_NUM_THREADS=2 lake --no-cache build R29MinimalBridge)
(cd epsilon && lake exe cache get && LEAN_NUM_THREADS=2 lake --no-cache build FullFamily)
(cd r29 && lake env lean --trust=0 AxiomAudit.lean)
(cd epsilon && lake env lean --trust=0 AxiomAudit.lean)
```

These commands download public dependencies and cached upstream objects. The
local source projects must start without `.lake/build` to constitute a clean
local rebuild. Cached upstream imports are not a clean upstream rebuild.
`--trust=0` is configured for every local library. A stricter fresh kernel replay,
when `leanchecker` is available in the pinned toolchain, can be run separately:

```sh
(cd r29 && lake env leanchecker --fresh --verbose R29MinimalBridge)
(cd epsilon && lake env leanchecker --fresh --verbose FullFamily)
```

`SOURCE_MANIFEST.json` records the full local import closure and exact source
hashes/Git blob identities. `PACKAGE_MANIFEST.json` also covers configuration,
audit harnesses, licensing and reproduction instructions. `verify_sources.py`
checks both manifests, import closure and forbidden proof-placeholder tokens.
Passing that Python check is **not** a Lean execution. See `VALIDATION.json` for
what was actually executed for this release; historical audit receipts remain
separate from fresh runs.

## Licensing and source boundaries

John Tripodo's formalization and software use the repository's existing MIT
license (`LICENSE`). The definition-only `r29/Erdos670Bridge/Statement.lean`
retains its Formal Conjectures copyright and Apache-2.0 notice; the full Apache
license is included. It is extracted from revision
`c77fdd446d23539302aa73bcfae4a9fa962b8382`, without importing the upstream
sorry-bearing theorem. Dependencies retain their own licenses and are fetched
from their public repositories, not redistributed here.

No private repository history, internal review correspondence, unrelated research,
compiled objects or credentials form part of this source package.
