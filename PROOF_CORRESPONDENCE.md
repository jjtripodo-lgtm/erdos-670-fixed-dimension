# Paper-to-Lean proof correspondence

This correspondence concerns the finite result in
[the current manuscript](paper/fixed_dimension_670.tex) and the exact
[66-module proof source](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean).
The source inventory is [here](verification/finite670/SOURCE_MANIFEST.json).

| Paper step | Formal source |
| --- | --- |
| Colex macro distances and positive-semidefinite reserve | `ColexPositivity`, `ColexReserveDirectCS`, `IncidenceBridge`, and the inherited finite Hardy/operator estimates |
| Whole-matrix completion and mutually orthogonal circle geometry | `Pass5CircleGeometry`, `Pass5CircleMacro`, `Pass5CircleConstruction` |
| Concrete finite parameters and scalar bounds | `Pass5Parameters`, `Pass5GeometryParameters`, `Pass5SpectrumParameters`, `Pass5CrossScalar` |
| Local ruler and within-cluster edge separation | `Pass5Ruler`, `Pass5Local`, `Pass5LocalEdges` |
| Cross-cluster separation and actual Euclidean construction | `Pass5CrossSeparation`, `Pass5ActualCrossSeparation`, `Pass5ActualConfiguration`, `Pass5FiniteAssembly` |
| Extension to every n ≥ 36354 in one fixed dimension | `Pass5Padding`, `Pass5FixedDimension670` |

All listed modules live under
`lean/Erdos488/Geometry/SeparatedDistances/`, with the fixed-dimension
modules in its `FixedDimension/` subdirectory. The historical directory name
`Erdos488` is a source identifier; the endpoint here concerns Problem 670.

The endpoint
`Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670`
has only the natural-number threshold hypothesis `36354 ≤ n`. It returns
`P : Fin n → EuclideanSpace ℝ (Fin 81794)`, injectivity, unit minimum
distance, `SeparatedConfiguration P`, a strict bound on every pair distance,
and `Metric.diam (Set.range P) < (147/200) * n^2`.
The separation predicate in `Defs.lean` compares genuinely distinct
unordered non-diagonal edges.

The [source-bound build summary](verification/finite670/LEAN_BUILD.json)
covers all 66 local modules and the final trust-zero axiom audit. It uses
cached upstream imports on one cloud computer; it does not transfer the
earlier version's two-machine or independent-kernel results to this theorem.
The [finite scalar audit](verification/finite670/validate_finite.py) is
supplementary arithmetic, not a replacement for the geometric proof.

## Exact conjecture consequence and later evidence

The [supplementary statement adapter](verification/statement_bridge/README.md)
adds the indexed-to-finite-set translation and proves
`Erdos670Bridge.erdos_670_negated` for the exact pinned upstream proposition.
It uses the unchanged finite theorem at epsilon = 1/4. The
[later public-adapter replay](verification/replay_20261017/README.md) has its
own 68-module source-build, full fresh official-kernel and endpoint-axiom
evidence; its separate-provider provenance is reported, not independently attested.

[Later internal formalizations](PUBLIC_STATUS.md) have different dimensions,
coefficients, size quantifiers and verification scopes. Their source closures
are not part of this paper-to-Lean correspondence or this public proof package.
