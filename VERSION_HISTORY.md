# Version history

## Documentation and replay-evidence update, 19 October 2026

[Current public status](PUBLIC_STATUS.md) explains the published fixed-dimensional
counterexample, exact conjecture-statement negation, and later internal R29 and
epsilon-family formalizations with their distinct quantifiers and source scopes.
The later internal proof closures are not added to this public package.

[The later public-adapter replay record](verification/replay_20261017/README.md)
adds source-bound evidence for the unchanged public theorem: a 68-module build
from zero local objects, full fresh official-kernel replay, and five standard-only
endpoint axiom audits, reported from a separate provider. Cached upstream imports
and unverified physical-host provenance remain explicit.

The manuscript, original proof, original receipts, tags, citation metadata,
Hexagon version, DOI archive, and licenses are unchanged. This update does not
claim external mathematical review or a new platform acceptance.

## Current finite version, 14 October 2026

*Orthogonal circles and a fixed-dimensional separated-distance counterexample*:
for every n ≥ 36354, a configuration in R^81794 with diameter strictly below
(147/200)n². The complete proof has 66 local Lean modules. Its source-bound
build uses upstream dependency cache on one cloud computer.

- [Current paper](paper/fixed_dimension_670.pdf)
- [Immutable finite proof source](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean)
- [Current verification scope](verification/finite670/README.md)
- [Hexagon preprint hexagon:2610.00254v1](https://hexagonmath.org/2610.00254?version=1), deposited 15 October 2026, with the same finite theorem stated above
- [Supplementary exact conjecture statement adapter](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/ce6a8d86f0da85af80e8f5b3752f7386a134e200/verification/statement_bridge/README.md), using the unchanged finite theorem

This revision does not claim a new DOI deposit or a new registry verification.
The current manuscript is CC BY 4.0 under [LICENSE-PAPER](LICENSE-PAPER).

## Archived v1.0.0, 12 October 2026

*Separated Euclidean distances with diameter below 0.74n² in a fixed dimension*:
for every n ≥ 68000, a configuration in R^458999 with diameter strictly below
(37/50)n². This earlier version has a 54-module proof closure and its own
macOS/Linux replay and independent-kernel evidence.

- [Complete immutable package](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/1e73a12ff1076dd11affadbf619ddbbef587133e)
- [Original v1.0.0 tag](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/v1.0.0)
- [Archived DOI 10.5281/zenodo.23329194](https://doi.org/10.5281/zenodo.23329194)
- [Original paper](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/1e73a12ff1076dd11affadbf619ddbbef587133e/paper/fixed_dimension_670.pdf)
- [Original verification record](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/1e73a12ff1076dd11affadbf619ddbbef587133e/verification/fixed670/REPLAY_STATUS.md)
- [Original manuscript license](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/1e73a12ff1076dd11affadbf619ddbbef587133e/LICENSE-PAPER)

Those immutable files, tags, DOI metadata, and rights remain unchanged.
The [separate compatibility repository](https://github.com/jjtripodo-lgtm/erdos-670-verification)
contains version-specific Palomar and Prove2Me checks of this earlier theorem.
Those results do not verify the revised finite constants.
