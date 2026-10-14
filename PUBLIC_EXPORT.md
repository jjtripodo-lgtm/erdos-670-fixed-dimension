# Public package provenance

The current package contains the finite-result manuscript, its complete
66-module local Lean proof closure, locked external dependencies, exact
source inventories, reproducibility checks, and scoped validation summaries.

The immutable finite proof source is
[commit f1604c368efce996a9af4d46f581e676e49054f5](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean).
Every one of its 70 Lean input files matches the source-bound recorded build
input map
`c025a9ccf45b4710dc5eb853c675e2de2a5966c784b46cecb19fda126ac7aa3b`.
The [module inventory](verification/finite670/SOURCE_MANIFEST.json) records
every source hash, Git blob, import, toolchain and dependency pin.
Historical inert provenance comments are retained in the exact source bytes.

`SOURCE_MANIFEST.json` at the repository root inventories the complete
current package. `python3 verify_release.py` checks its SHA-256 hashes and
byte counts; the finite source verifier separately checks the exact import
closure and build-summary consistency. No private repository, runtime path,
external receipt, or credential is needed to run these checks.

The build summary discloses cached upstream dependencies and one-machine
scope. It is not an independently authenticated execution certificate.
The paper's three byte-identical final build passes in one directory and
visual checks are recorded separately; they are
not Lean replay or independent mathematical review.

The previous complete package remains available from its immutable
[version-history links](VERSION_HISTORY.md). No existing tag or DOI record
is replaced. The current manuscript's [CC BY 4.0 grant](LICENSE-PAPER)
applies only to this revised finite version; software remains
[MIT licensed](LICENSE).
