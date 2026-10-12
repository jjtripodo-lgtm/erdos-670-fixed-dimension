# Public package provenance

This repository contains the manuscript, the 54-module Lean closure of the final theorem, and its verification material. Its initial public commit has no private Git ancestry. `CANDIDATE_SHA256.json` inventories the exact selected files; `python3 verify_candidate.py` checks their hashes and byte counts.

`verification/fixed670/SOURCE_MANIFEST.json` records the development source commit, Git blob IDs, and SHA-256 hashes. It and one verbatim Lean source comment retain an owning-repository identifier for provenance. All source modules, locks, and scripts needed for the included checks and replay are present here; access to that development repository is not required. The execution receipt records dependency checkout identities but does not authenticate precompiled upstream cache provenance.

The [MIT license](LICENSE) governs code and formalization. The manuscript source and PDF carry the [separate reserved-rights terms](LICENSE-PAPER).
