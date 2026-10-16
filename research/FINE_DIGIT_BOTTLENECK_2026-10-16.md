# Discovery note: the fine-digit bottleneck (16 October 2026)

This is an exploratory algebraic diagnosis of the *existing* finite construction, not a new Erdős 670 theorem or a Lean proof.

## Exact parameter calculation

The current finite scalar witness has
`s=9/8`, `tau=9999/10000`, and `lambda=853589/960000`.
Its fine-digit separation slack is exactly

```
tau*s*lambda - 1 = 5109233/25600000000
                        ≈ 0.0001995794140625.
```

The leading coefficient is exactly `24057/32768 ≈ 0.734161376953125`.
The all-n padded coefficient recorded in `validate_finite.py` is
`220816318833/300740452352 ≈ 0.7342421583330824`, leaving
`147/200 - padded ≈ 0.0007578416669176242`.

## Derived necessary constraint within this certificate template

If the criterion continues to require `tau*s*lambda > 1`, then
`s > 1/(tau*lambda)`. Holding `tau`, `lambda`, and the macro offset ratio
`K/m²` fixed, the leading coefficient `s³(1/2 + K/m²)` is strictly
increasing in `s`. Thus the coefficient-optimal *admissible limit*
under those fixed inputs is approached as `s` decreases to
`1/(tau*lambda)`; it is not attained because the inequality is strict.

This is a conditional optimization fact, **not** a license to change `s`
without rechecking C2-C5, the radius/completion bounds, and finite padding:
`tau` and `lambda` themselves depend on other geometric parameters.

## Discovery hypothesis

The fine-digit guard has slack only about 2e-4. A promising next search is a
coupled rational-parameter optimization that increases `lambda` (via the
ruler/chord distortion bounds), then lowers `s` and recomputes the entire
finite certificate. Optimizing `s` alone is unsafe. A second independent
axis is reducing the macro offset `K/m²` without violating Gram positivity.

## Falsifiable next experiment

Implement a rational-only parameter sweep over `(s,a,L,C,m0,B)` and compute
all existing guards exactly, including the derived tau bound and all-n
padding. Report Pareto improvements in (dimension, threshold, coefficient).
Every candidate must be validated against the *complete* criterion and Lean
formalization before being called a theorem.

No GitHub Actions, cloud build, external submission, or verification status
is asserted by this note.
