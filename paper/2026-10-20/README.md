# Separated distances in fixed dimension

John Tripodo. GitHub manuscript, 20 October 2026.

[Read the PDF](Separated_Distances_in_Fixed_Dimension.pdf) · [Complete editable source ZIP](Separated_Distances_in_Fixed_Dimension_source.zip) · [Theorem scopes and exact sources](SOURCE_MAP.md)

The paper gives the two-circle epsilon family and its uniform form, the R29 prime-first construction, and a separate all-size R29 corollary. Its common ruler/chord lemmas, macro appendix and rational reconstruction program make the written arguments self-contained. No new theorem discovery, independent specialist review or Lean execution is claimed.

## Reproduce

Use a standard TeX Live installation with the packages named in `preamble.tex` (including Latin Modern and Palatino), plus Python 3. From this directory:

```sh
python3 assemble_manuscript.py
python3 certificate_reconstruction.py
python3 -O certificate_reconstruction.py
python3 verification/check_readability.py
pdflatex -interaction=nonstopmode -halt-on-error Separated_Distances_in_Fixed_Dimension.tex
pdflatex -interaction=nonstopmode -halt-on-error Separated_Distances_in_Fixed_Dimension.tex
```

The modular source is `preamble.tex`, `main_body.tex`, the three appendix/source files, and `references.tex`; the assembly script creates the complete TeX. All required local inputs are included in the ZIP. The exact certificate reconstructs 15 positive rational pivots and 12 scalar guards. The scoped checker compares original certificate identities, checks exact epsilon/padding inequalities and runs 120 finite ruler regression controls. The finite controls supplement the written universal argument; they are not a proof by exhaustive sampling or a Lean replay.

The [recorded validation](verification/PAPER_VALIDATION.json) describes this release's build, visual inspection and exact checks. The older public package and formalization records remain at their existing paths. Newer Lean declaration excerpts and audit receipts are in the repository's [existing supplement](../../verification/internal_supplements/README.md); the newer full Lean closures remain private.

## Versions and rights

This is a new GitHub manuscript. The [Hexagon v1 paper](https://hexagonmath.org/2610.00254?version=1) identifies the earlier finite-result version, not this 20 October paper. The original Zenodo deposit (DOI `10.5281/zenodo.23329194`) and the separate 20 October deposit (DOI `10.5281/zenodo.23490573`) were voluntarily withdrawn on 22 October 2026; these identifiers are retained only as historical provenance and are not active archive or preferred citation destinations. See the repository [version history](../../VERSION_HISTORY.md).

The paper and its included supporting files are [CC BY 4.0](LICENSE.md). Existing versions retain their own grants; see [public package provenance](../../PUBLIC_EXPORT.md).
