# Public package provenance

The package retains the finite-result manuscript, its complete
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

The original build summary discloses cached upstream dependencies and one-machine
scope. It is not an independently authenticated execution certificate. The
later [public-adapter replay export](verification/replay_20261017/README.md)
preserves a separate receipt and normalized logs with explicit original-byte
hashes. Separate-provider provenance is reported, not independently attested.
The internally formalized R29 and epsilon-family endpoints are summarized in
[PUBLIC_STATUS.md](PUBLIC_STATUS.md); their proof closures are not distributed here.
The 14 October finite paper's three byte-identical final build passes in one directory and
visual checks are recorded separately; they are
not Lean replay or independent mathematical review.

The previous complete package remains available from its immutable
[version-history links](VERSION_HISTORY.md). No existing tag or DOI record
is replaced. The 14 October finite manuscript's [CC BY 4.0 grant](LICENSE-PAPER)
remains specific to that version; software remains
[MIT licensed](LICENSE).

## Additive manuscript version, 20 October 2026

The new files under `paper/2026-10-20/` contain the readable two-circle/R29 paper, modular and assembled LaTeX, figures, exact arithmetic reconstruction/checks, and source/version maps. The finite macro appendix is inherited from the unchanged public finite manuscript. Only the source and certificate material needed for this paper is exported; complete private Lean closures and unrelated research are not included.

The new written all-size R29 corollary relies on Dusart's published prime-interval theorem and exact padding arithmetic. It has no Lean endpoint. The new paper's local build/layout and arithmetic checks are recorded in its `verification/PAPER_VALIDATION.json`; these do not transfer old Lean receipts to new text.

The owner approved CC BY 4.0 for the new paper and its included supporting files; the [new version-specific grant](paper/2026-10-20/LICENSE.md) records it. Existing licenses and grants remain unchanged, including `LICENSE-PAPER` for the 14 October finite version and MIT grants for software. No existing tag, DOI, Hexagon version or immutable archive is replaced.
