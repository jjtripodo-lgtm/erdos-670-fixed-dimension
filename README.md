# Fixed-dimensional separated Euclidean distances

**Current public preprint:** [*Separated distances in fixed dimension*, Hexagon v2 (hexagon:2610.00254v2)](https://hexagonmath.org/2610.00254v2) · [Immutable 20 October GitHub PDF](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/12730b904260f3c10ff2259c49415a20df755ae7/paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf) · [Reader and scoped-review guide](READER_GUIDE.md) · [John Tripodo's ORCID](https://orcid.org/0009-0006-9180-4953).

**Version distinction:** Hexagon [v1](https://hexagonmath.org/2610.00254v1) is the earlier finite-dimension 81,794 theorem; current **v2** contains the later two-circle tolerance family and dimension-29 results. The PDF above is a pinned GitHub file; exact PDF-byte identity across hosts has not been established. Hexagon has assigned no DOI. 

**Other papers:** [Double Hall](https://github.com/jjtripodo-lgtm/double-hall-optimal-degree) · [Sparse determinants](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants).

**Erdős #670, under the maintained fixed-dimension interpretation:** the
published construction is a counterexample, with a Lean proof and an exact
conjecture-statement adapter. [Current explanation and formalization status](PUBLIC_STATUS.md)
separate the published theorem, later internal extensions, and review limits.

## New paper, 20 October 2026

**[Separated distances in fixed dimension](paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf)**, by John Tripodo, gives a readable common proof framework for the later two-circle family and dimension-29 construction.

- For each 0 < epsilon <= 1/2, set m = ceil(8192/epsilon). Every n >= 4m has a configuration in R^(10m-1) with diameter < (1/2+epsilon)n². Dimension depends on epsilon, not n.
- In R^29, arbitrarily large selected sizes have diameter < 0.998n². This is the exact prime-first Lean endpoint.
- A separate written corollary gives diameter < 0.999n² in R^29 for every n >= 400000, using Dusart's explicit prime-interval theorem. This all-size corollary is not a Lean endpoint.

Every statement includes minimum point distance at least one and separation of genuinely different unordered edge lengths. The family and written all-size corollary have strict gaps > 1; the stated formal R29 subsequence endpoint has gaps >= 1.

[Editable source and checks](paper/2026-10-20/README.md) · [Source ZIP](paper/2026-10-20/Separated_Distances_in_Fixed_Dimension_source.zip) · [Exact scope and source map](paper/2026-10-20/SOURCE_MAP.md)

The newer Lean proof closures remain private; their existing public statement excerpts and audit records are linked below. No new Lean run or independent specialist review is claimed. The current Hexagon v2 preprint presents the later 20 October mathematical claims; Hexagon v1 and the two withdrawn Zenodo deposits remain separate historical records. Existing paper and proof URLs remain unchanged.

## Earlier finite result, retained unchanged

For every integer **n ≥ 36354**, there is an injectively indexed configuration
of n points in the single fixed Euclidean space **R^81794**. Distinct points
are at least one unit apart; lengths of distinct unordered non-diagonal edges
differ by at least one; and both every pair distance and the actual set
diameter are strictly below **(147/200)n² = 0.735n²**.

**[Read the 14 October finite paper](paper/fixed_dimension_670.pdf)** ·
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
upstream dependency cache on one cloud computer.
A clean upstream source rebuild and independent specialist review are not
established by that run. A [later replay of the exact public adapter](verification/replay_20261017/README.md)
records another zero-local-object build and full fresh official-kernel replay,
reported from a separate provider; physical host identity is not independently
attested. The original distributed record is a sanitized
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

## Exact conjecture statement adapter

The supplementary [statement bridge and reproducibility package](verification/statement_bridge/README.md)
proves the negation of the exact fixed-dimension proposition extracted from
Formal Conjectures at its pinned revision. It uses the unchanged finite theorem
above, with a finite-set translation and epsilon = 1/4.

A new source-bound build of 68 local modules, official fresh-kernel replay, and
transitive axiom audit passed; all five audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. The package records dependency-cache reuse
and the Lean/Mathlib version boundary. It is not a full build or accepted submission
in the newer upstream Formal Conjectures project.

```sh
python3 verification/statement_bridge/verify_package.py
```

The package includes exact inputs, normalized execution logs, and instructions
for a fresh replay. The original finite source closure and checks remain unchanged.

## Attribution, review, and rights

The author thanks Boon Suan Ho for helpful comments on an earlier draft of this manuscript.

This is AI-assisted research. See the manuscript's disclosure for the author's
role and the limits of human review; the formal checks do not establish
independent mathematical or priority review, journal acceptance, or platform
endorsement. [Prior work](PRIOR_ART.md) and the
[dated source-access ledger](CITATIONS.md) distinguish the fixed-dimensional
claim from Ho's growing-dimensional result and identify classical ingredients.

The 14 October finite manuscript is licensed under
[CC BY 4.0](LICENSE-PAPER). Code and formalization remain [MIT licensed](LICENSE);
dependencies retain their own licenses. Use [CITATION.cff](CITATION.cff) for
version-specific citation metadata.

## Version history

[The 19 October documentation update](PUBLIC_STATUS.md) records the exact
statement bridge, later replay evidence, and separately scoped internal
dimension-29 and epsilon-family formalizations. That update did not revise the
14 October finite manuscript.

[Version history](VERSION_HISTORY.md) links the immutable earlier v1.0.0
manuscript, proof, verification records, and DOI archive. Their original
claims, evidence, and manuscript license remain version-specific.
