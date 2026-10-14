# Current manuscript validation

The 14 October 2026 finite-result manuscript is
`paper/fixed_dimension_670.tex`, with matching PDF and a source-only ZIP.
All three files are included and their hashes appear in
[PAPER_VALIDATION.json](PAPER_VALIDATION.json) and the root package manifest.

- TeX SHA-256: `1061fd4ecf720a36612291eff14f56c0dce37e4dd4b46afd3625c73a2710d6f0`
- PDF SHA-256: `25b802230e7fd49a478c589132726bcf743322a0126018e7c3e63dc89b509843`
- Source ZIP SHA-256: `6c1e60bf484bafc708d20924b0543f25ff7848fc39b893825811891a32b7d6b7`

The final three fixed-epoch pdfLaTeX passes produced byte-identical 17-page
PDFs. All pages were rendered and reviewed in a contact sheet, and pages
1, 2, 9, 14, and 17 were inspected individually. There were no undefined
references or citations, missing glyphs, or overfull boxes. One harmless
underfull bibliography box remains.

The source comparison preserves the finite mathematics. Five reference-type
annotations correct Lemma/Remark/Proposition display while preserving all 78
existing label numbers. The exact approved acknowledgment appears once:

> The author thanks Boon Suan Ho for helpful comments on an earlier draft of this manuscript.

The paper links its finite Lean endpoint to immutable public proof commit
`f1604c368efce996a9af4d46f581e676e49054f5`; its separate `1e73a12` citation
identifies only the earlier manuscript. Exact-rational and source checks
passed in normal and optimized Python modes, with three negative controls.
The source ZIP contains exactly `orthogonal_circles.tex`, byte-identical to
the published TeX despite the different archive filename.

The build receipt retains the original relative build filenames for accurate
reproduction. Published files have been renamed without changing their bytes.
This paper-only validation is not a new Lean replay, independent specialist
review, journal submission, or acceptance. The unchanged proof inputs have
their own [scoped build record](../finite670/README.md).
