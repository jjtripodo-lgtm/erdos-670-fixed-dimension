# Public clean-history selection record

This repository contains the selected files from the corrected private candidate, released with the owner's approval after review of the file selection, attribution, and separate code and manuscript terms. This document records that selection and its provenance; the manuscript remains a research work awaiting independent mathematical review.

The existing development repository and its branch and PR history remain private. This public project began with a fresh Git history containing selected file bytes only; `.git`, branch history, issue comments, internal audit folders, and local `.lake` caches were excluded.

## Selected path allowlist, relative to this candidate root

- Root: `README.md`, `PRIOR_ART.md`, `CITATIONS.md`, `CITATION.cff`, `LICENSE`, `LICENSE-PAPER`, `PROOF_CORRESPONDENCE.md`, `PUBLIC_EXPORT.md`, `verify_candidate.py`.
- Paper: `paper/fixed_dimension_670.tex`, `paper/fixed_dimension_670.pdf`.
- Formal source: `lean-fixed670/Erdos488/**/*.lean`, `lean-fixed670/AxiomAudit.lean`, `lean-fixed670/lakefile.toml`, `lean-fixed670/lake-manifest.json`, `lean-fixed670/lean-toolchain`, `lean-fixed670/replay.py`, `lean-fixed670/replay_contract.py`, `lean-fixed670/prepare_dependencies.py`, `lean-fixed670/verify_sources.py`, `lean-fixed670/.gitignore`.
- Source and replay checks: `verification/fixed670/FROZEN_FILES_SHA256.json`, `SOURCE_MANIFEST.json`, `upstream-lake-manifest.json`, `upstream-lean-toolchain`, `SOURCE_PIN.md`, `REPLAY_STATUS.md`, `verify_execution.py`, `negative_tests.py`, and every regular file under `verification/fixed670/execution/`.
- Manuscript checks: `verification/manuscript670/VALIDATION.md`, `check_manuscript.py`, `arithmetic_and_references.json`, `tectonic-a.stdout.log`, `tectonic-a.stderr.log`, `tectonic-b.stdout.log`, `tectonic-b.stderr.log`, `tectonic-final.log`.
- `CANDIDATE_SHA256.json` inventories the selected files, recomputed with `verify_candidate.inventory()` after the public wrapper edits. The read-only checks in the README validate the final copy.

## Deliberately excluded private/history material

Internal WIP notes, source-export utilities, integration logs, historical review reports, old diffs, and surrounding repository files are outside the allowlist, as are `.git/`, `.lake/`, generated builds/renders, and local absolute-path records. Preserve the historical originals privately; do not silently edit them into a new claim.

The selected `SOURCE_MANIFEST.json` intentionally retains the original source commit, Git blob IDs, SHA-256 hashes and an owning-repository identifier as provenance; one verbatim Lean source comment also names that development repository. These are source identities, not access credentials. All 54 module bytes, locks and scripts are included, so verifying and replaying the selected copy does **not** require access to that repository. The execution receipt records exact checkout HEADs, but it does not authenticate the ancestry of precompiled dependency caches. The final selected tree was checked for links, PDF metadata, source manifest, paper, proof statement, licenses, and exact file inventory before release.

The existing code and paper license files were inherited byte-for-byte from the private selected packet and approved by the owner for this release. The code is MIT-licensed; the manuscript rights are reserved under `LICENSE-PAPER`. No broader manuscript license is granted here.
