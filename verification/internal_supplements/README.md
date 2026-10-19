# Exact records for the later internal formalizations

This supplement identifies the sources behind the internal-result table in
[PUBLIC_STATUS.md](../../PUBLIC_STATUS.md). It publishes exact statement
excerpts and recorded endpoint audit output, **not the proof closures**.
These records do not enable an independent Lean replay of those results.

| Result | Exact statement record | Recorded audit output |
| --- | --- | --- |
| R29 unbounded subsequence, finite-set translation, exact conjecture negation | [R29_STATEMENTS.txt](R29_STATEMENTS.txt) | [R29_ENDPOINT_AUDIT.log](R29_ENDPOINT_AUDIT.log) |
| Arbitrary-epsilon and uniform-dimension families | [EPSILON_STATEMENTS.txt](EPSILON_STATEMENTS.txt) | [EPSILON_ENDPOINT_AUDIT.log](EPSILON_ENDPOINT_AUDIT.log), [full-family axiom output](EPSILON_FULL_FAMILY_AXIOMS.log) |

The original [R29 minimal build receipt](R29_MINIMAL_BUILD_RECEIPT.json)
records 60 local modules, zero initial local objects, and exit 0, with
cached upstream imports. The [later minimal build log](R29_LATER_BUILD.log)
records 3,562 jobs and the minimal adapter's two standard-only axiom sets;
the [later fresh-replay log](R29_LATER_FRESH.log) identifies its target.
The separate-provider report records that fresh command's exit as zero;
the one-line replay log alone does not attest completion or host identity.
Its report hash is recorded in SOURCE_RECORDS.json.

The [epsilon-family receipt](EPSILON_FINAL_RECEIPT.json) binds the full-family
source and audit hashes, flags, endpoint names and review limits. Its
historical import reuse must not be read as a fresh proof-closure rebuild.

[SOURCE_RECORDS.json](SOURCE_RECORDS.json) binds each excerpt to the original
source's Git blob and SHA-256, and each audit output to its original blob
and published bytes. The headers are copied exactly, with proof bodies
omitted. Namespace and predicate names retain their original spelling.
The public adapter's [statement extraction](../statement_bridge/lean/Erdos670Bridge/Statement.lean)
contains the fixed-dimensional proposition used by both exact negations.

For R29, `Erdos670R29.r29_unbounded_counterexamples` includes injectivity,
unit minimum distance and actual set diameter; the minimal finite-set
adapter has a different namespace and does not repeat the minimum-distance
conclusion in its output type. These are compatible statements, not
interchangeable exported declarations. An unbounded subsequence suffices
for the eventual-quantifier contradiction. The number 600 is a lower bound
on the selected sizes, not an all-size threshold.

For the epsilon-family, the exact codomain and numerical thresholds are in
the source headers even where Lean's printed audit output elides the
codomain after an existential. All construction hypotheses have been
discharged in the final endpoint. Recorded final audit axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

These excerpts and logs were checked against the retained internal source
identities on 19 October. That check did not execute Lean. The source and
audit records report prior scoped Lean runs with cached imports; they do
not establish an independent implementation of the kernel, human proof or
priority review, external acceptance, or a new public manuscript version.
