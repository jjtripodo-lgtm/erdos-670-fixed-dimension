# Fixed-dimensional separated Euclidean distances

## Current finite result

For every integer **n ≥ 36354**, there is an injectively indexed configuration
of n points in the single fixed Euclidean space **R^81794**. Distinct points
are at least one unit apart; lengths of distinct unordered non-diagonal edges
differ by at least one; and both every pair distance and the actual set
diameter are strictly below **(147/200)n² = 0.735n²**.

**[Read the paper](paper/fixed_dimension_670.pdf)** ·
[TeX source](paper/fixed_dimension_670.tex) ·
[exact Lean theorem](lean/Erdos488/Geometry/SeparatedDistances/FixedDimension/Pass5FixedDimension670.lean)

The manuscript is *Orthogonal circles and a fixed-dimensional
separated-distance counterexample*, by John Tripodo. It gives the finite
construction and proof, with exact sufficient constants. No least-dimension,
optimal-coefficient, or arbitrary-parameter extension is claimed.

## Proof and verification

The complete local Lean source closure is included in [lean/](lean/):
66 modules, with all nine external dependency revisions locked. The exact
declaration is
`Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670`.

A [recorded source-bound build](verification/finite670/LEAN_BUILD.json)
compiled all 66 local modules from zero local project objects at trust level
zero and completed the endpoint axiom audit. Its only endpoint axioms were
`propext`, `Classical.choice`, and `Quot.sound`. The 3,502-job build reused
upstream dependency cache on one cloud computer. A clean upstream rebuild,
second-machine replay, and independent specialist review have not been
performed for this finite version. The distributed record is a sanitized
summary, with the exact checked input hashes; raw runtime logs are not bundled.

- [Paper-to-Lean correspondence](PROOF_CORRESPONDENCE.md)
- [Source inventory and reproduction instructions](verification/finite670/README.md)
- [Current paper validation](verification/manuscript670/CURRENT_VALIDATION.md)
- [Public package provenance](PUBLIC_EXPORT.md)

From the repository root:

```sh
python3 verify_release.py
python3 verification/finite670/verify_sources.py
python3 verification/finite670/validate_finite.py
```

These are offline identity, closure, recorded-scope, and exact-rational checks.
To compile the proof, use the pinned toolchain and dependency lock:

```sh
cd lean
lake --no-cache build
lake env lean --trust=0 AxiomAudit.lean
```

The [reproduction guide](verification/finite670/README.md) explains clean local
builds and upstream-cache scope. The public proof source is immutably pinned at
[commit f1604c368efce996a9af4d46f581e676e49054f5](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean).

## Attribution, review, and rights

The author thanks Boon Suan Ho for helpful comments on an earlier draft of this manuscript.

This is AI-assisted research. See the manuscript's disclosure for the author's
role and the limits of human review; the formal checks do not establish
independent mathematical or priority review, journal acceptance, or platform
endorsement. [Prior work](PRIOR_ART.md) and the
[dated source-access ledger](CITATIONS.md) distinguish the fixed-dimensional
claim from Ho's growing-dimensional result and identify classical ingredients.

The current finite manuscript is licensed under
[CC BY 4.0](LICENSE-PAPER). Code and formalization remain [MIT licensed](LICENSE);
dependencies retain their own licenses. Use [CITATION.cff](CITATION.cff) for
current-version citation metadata.

## Version history

[Version history](VERSION_HISTORY.md) links the immutable earlier v1.0.0
manuscript, proof, verification records, and DOI archive. Their original
claims, evidence, and manuscript license remain version-specific.
