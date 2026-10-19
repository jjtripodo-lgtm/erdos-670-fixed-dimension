# Later replay of the published exact statement adapter

Recorded execution: 17 October 2026, 17:58:11–18:19:05 UTC.
Evidence published with the 19 October documentation reconciliation.

## Source and outcome

The depositing report identifies the environment as a Claude-operated
Anthropic Linux x86_64 container, 2 vCPU, separate from the original run's
provider and computer. That is reported provenance, not an independently
attested physical-host identity or specialist review.

The checkout was public commit
`ce6a8d86f0da85af80e8f5b3752f7386a134e200`, using the unmodified
[public replay assembler and runner](../statement_bridge/README.md).
The recorded 72-input source manifest hash is
`0908cd731253b100d0deb6d378b2df945380fae56f2941b6f55c0f3d0d2ea75b`,
identical to the original public statement-bridge manifest.

The retained [execution receipt](BUILD_RECEIPT.json) records:

- Zero initial local project objects; all 68 local modules built, 3,504 jobs,
  with local source trust level zero.
- `lake env leanchecker --fresh --verbose Erdos670Bridge.Bridge`, exit 0.
- Five transitive endpoint axiom reports, each containing only `propext`,
  `Classical.choice`, and `Quot.sound`.

The first attempt stopped before Lean because zstd was missing. Its
[failure log](runner_stdout_FAILED_first_attempt_missing_zstd.log) is retained.
The subsequent completed run is recorded separately in [runner_stdout.log](runner_stdout.log).

## Receipt labels and export normalization

`BUILD_RECEIPT.json` is preserved byte-for-byte. Its fields
`same_cloud_computer: true`, `independent_second_machine_replay: NOT_RUN`,
and the workspace-reconstruction label were static runner output, not
measurements of this environment's identity or its relationship to the
original run. We preserve those fields and disclose the depositing report
rather than silently relabeling the receipt. Its command results, durations,
source binding, and log hashes are specific to the later execution.

Published logs replace only the absolute run-directory prefix with
`$WORKSPACE`. [LOG_NORMALIZATION.json](LOG_NORMALIZATION.json) binds their
original Git blob IDs, original SHA-256 hashes, and published hashes.
Receipt log paths are relative to the original runner layout; the files
here are flattened to their basenames. Receipt log hashes refer to the
original bytes and are reconciled through that normalization map.

The 19 October check matched every selected original file to its retained
source blob and SHA-256 inventory, checked the receipt against the unchanged
public input manifest, and checked all command/log/axiom bindings. This is
an evidence audit, not another Lean execution.

## Limits

Upstream dependency caches were reused. No clean source rebuild of all
upstream dependencies, independently implemented kernel, full newer Formal
Conjectures project build, or human specialist proof/priority review is
established. See the public [fresh-kernel scope](../statement_bridge/verification/LEAN_CHECKER_SCOPE.md).
This replay concerns the public R^81794 theorem and exact adapter only;
it does not certify the later internal R29 or epsilon-family packages.
