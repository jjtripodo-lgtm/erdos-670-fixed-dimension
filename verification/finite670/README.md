# Finite-result source and verification scope

This directory records the finite theorem for every `n >= 36354` in fixed
dimension `81794`, with diameter strictly below `(147/200)n^2`.
Its exact declaration is
`Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670`.

`SOURCE_MANIFEST.json` inventories all 66 local modules and all 70 Lean input
files under `../../lean/`. It records SHA-256, Git blob IDs, the exact local
import graph, Lean `v4.31.0-rc1`, and the locked Mathlib revision.
No compiled proof objects or upstream caches are distributed.

`LEAN_BUILD.json` is a sanitized summary of a recorded build of these exact
inputs. Starting with zero local project objects, all 66 local modules built
with trust level zero; the build completed 3,502 jobs, and the endpoint axiom
audit passed with only `propext`, `Classical.choice`, and `Quot.sound`.
The build reused upstream dependency cache on one cloud computer. A clean
upstream rebuild, second-machine replay, and independent specialist review
have not been performed. Raw runtime logs are not distributed; the summary is
not an independently authenticated execution certificate.

## Check source identity and arithmetic

From the repository root, with Python 3:

```sh
python3 verification/finite670/verify_sources.py
python3 verification/finite670/validate_finite.py
```

The first checks the input inventory, hashes, exact transitive closure, pins,
and consistency of the recorded build scope. The second checks exact finite
rational margins. Neither command reruns Lean or constitutes a geometric proof.

## Rebuild the proof

Install the official pinned Lean toolchain. With network access to the public
dependencies in the lockfile and sufficient disk space:

```sh
cd lean
lake --no-cache build
lake env lean --trust=0 AxiomAudit.lean
```

Use a clean checkout with zero local project `.olean` files to reproduce the
reported local-source scope. Do not run `lake update`: preserve the committed
dependency lock. Obtaining cached upstream imports is optional; it changes
which dependencies are built from source and must be disclosed in any new
replay report. All local proof modules are always built at trust level zero.

