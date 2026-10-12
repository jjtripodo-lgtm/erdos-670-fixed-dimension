# Fixed-dimension #670 source pin

The owning development snapshot exported here is
`35c67a69e009c9ca27267077608864987b7e2851`. The private source
export process checked a clean checkout at that commit, recursively followed
the final theorem module's local imports, checked every file against its Git
blob, and wrote 54 verbatim project modules. Exact module hashes, Git blobs,
imports, and paths are in `SOURCE_MANIFEST.json`.

The theorem is
`Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670`.
Its final source file `SourceFixedDimension670.lean` remains SHA-256
`97cfb0df31070d64c6a48cac85de205745e7ab8a267a7c8720891893050ddd58`.
The theorem gives every `n ≥ 68000` an injective `Fin n` family in
`EuclideanSpace ℝ (Fin 458999)`, minimum nonzero distance at least one,
unit gaps on distinct non-diagonal unordered edges, and diameter strictly
below `(37/50)n²`.

The final dependency path uses
`colex_incrementGram_ge_half_tridiagonal_direct` in `IncidenceBridge.lean` and
`source_actual_operator_completion_universal_B_matrix` from
`SourceQuadraticMatrix.lean` in both relevant `SourceActualCrossMetric.lean`
calls. The latter uses the source whole-family B budget. The path continues
through the actual spectrum, separation, diameter, and all-n modules to the
final theorem.

Lean is pinned to `leanprover/lean4:v4.31.0-rc1`. The exact owning-source
lockfile is `upstream-lake-manifest.json`, SHA-256
`b091eb307e6a7fe5a0d4bf3245aaa63d3f2810df242cc55cd017ffd1e06974a3`.
The standalone `lean-fixed670/lake-manifest.json`, SHA-256
`a6eaf4622922b9e2a9eba5b5f09cbabb721be6b85bca5184e2799ddbcfc1b302`,
has the same nine dependency objects and changes only the Lake package name
to `erdos670_fixed`. Mathlib is exactly
`0ed37c9258f123a2c76a2175596f75c2bd50f941`.

The macOS [execution receipt](execution/RECEIPT.json) and independent Linux
[evidence bundle](independent-linux-20261012/README.md) bind their runs to the
same source and nine pinned clean dependency checkouts. See
[REPLAY_STATUS.md](REPLAY_STATUS.md) for the project builds, axiom audits,
fresh kernel check, and dependency-cache scope.

All source modules, locks, and verification scripts needed for replay are
present here; access to the owning development repository is not required.
