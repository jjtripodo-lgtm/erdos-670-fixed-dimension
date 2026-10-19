# Exact Formal Conjectures statement adapter

The theorem `Erdos670Bridge.erdos_670_negated` negates the exact fixed-dimension
conjecture type in [Formal Conjectures commit c77fdd4](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/670.lean),
Git blob `1ae473043edcd960c0b9eed81ccd6e82994f2a22`.

The adapter uses the existing finite theorem in this repository: in the same
Euclidean dimension 81794, every n >= 36354 has a separated configuration of
diameter < (147/200)n². It converts the indexed configuration to a finite set,
proves the cardinality and exact point-pair separation predicate, and transports
set-range diameter. At epsilon = 1/4, the conjecture would eventually require
at least (3/4)n², a contradiction.

## Exact statement, distinct environment

`lean/Erdos670Bridge/Statement.lean` extracts only the upstream definition and
conjecture type. A byte-level source checker verifies the definition and type
against the immutable upstream snapshot in `upstream/670.lean.txt`. The displayed
full negation is also checked, allowing only namespace qualification and whitespace.
No Formal Conjectures module or its unproved `erdos_670` theorem is imported.

The existing proof remains on Lean 4.31.0-rc1, Mathlib
`0ed37c9258f123a2c76a2175596f75c2bd50f941`. The pinned Formal Conjectures project
uses Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
This is an exact textual statement bridge verified in the proof's pinned environment.
It is not a build, accepted submission, or complete cross-version integration in
the current upstream project.

## Recorded verification

The source-bound run is recorded in `verification/BUILD_RECEIPT.json` and its four
logs. All 68 local modules were compiled from zero local project objects, including
the 66 unchanged geometric modules, using trust level zero. The bundled official
`leanchecker --fresh` additionally replays the final target and loaded safe,
non-partial declaration closure into a fresh kernel environment. The subsequent
transitive axiom audit covers the original finite endpoint and four adapter endpoints;
each uses only `propext`, `Classical.choice`, and `Quot.sound`.

The record is a new execution after an earlier ephemeral workspace was lost; no
previous PASS was reused to certify these bytes. The frozen Lean manifest contains
72 actual inputs: 66 original modules, two bridge modules, AxiomAudit and three Lake/
toolchain configuration files. The original finite verifier's 70-input snapshot is
unchanged; this supplementary replay is assembled separately.

Upstream compiled dependency caches were reused. That original run is not a clean
upstream source rebuild, independently implemented kernel check, second-machine run
or specialist review. A [later replay record](../replay_20261017/README.md) adds a
successful repeat build and full fresh replay, reported from a separate provider,
with its own provenance limits. The precise checker semantics and official executable/source hashes are in
`verification/LEAN_CHECKER_SCOPE.md` and `TOOLCHAIN_BINARY_HASHES.json`.

Published logs replace the local absolute workspace prefix with `$WORKSPACE` only.
`LOG_NORMALIZATION.json` records both raw receipt-bound hashes and published hashes.
The original execution receipt is unchanged. File hashes and recorded commands are
reproduction evidence, not independent certification.

## Quick offline check

From the repository root:

```sh
python3 verification/statement_bridge/verify_package.py
```

This checks package inventory, unchanged geometric inputs, source/receipt bindings,
and log hashes. It does not execute Lean. The original README's finite proof and
release checks continue to apply separately.

## Execute the full replay

Prerequisites: Linux x86_64, Python >=3.11, Git, GNU tar with zstd, at least 12 GiB
free disk and 8 GiB RAM. Downloads use only the pinned official Lean release,
locked public source repositories and Mathlib cache. No credentials or paid CI are needed.

```sh
python3 verification/statement_bridge/assemble_replay.py /absolute/new/replay-directory
cd /absolute/new/replay-directory
python3 scripts/bootstrap.py
python3 scripts/run_verification.py
```

The destination must be new and outside the public checkout. Assembly copies and
checks all 72 source/config inputs but performs no download or build. Bootstrap
verifies the pinned official release archive before installing its full distribution,
then fetches all nine dependency revisions without updating the lockfile.

The runner downloads the selected dependency cache, executes `lake --verbose --no-cache build`
with both local libraries configured for `--trust=0`, runs
`lake env leanchecker --fresh --verbose Erdos670Bridge.Bridge`, then
`lake env lean --trust=0 AxiomAudit.lean`. It refuses to overwrite a prior run receipt
or reuse local project object files, maintains a 512 MiB disk reserve, and records
commands, return codes, durations, hashes and explicit assurance limits. A fresh
`status: PASS` requires all checks to succeed. Preserve failed receipts separately.

## Licensing

Existing proof/code retains the repository's MIT license. The extracted upstream
statement and retained upstream source keep their Apache-2.0 copyright header and
`upstream/LICENSE`. Existing paper rights, authorship, version history, tags and DOI
records are unaffected by this supplementary verification package.
