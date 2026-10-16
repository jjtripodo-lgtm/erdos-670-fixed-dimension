# Discovery: a matching dimension-exponent barrier inside the five-condition certificate

16 October 2026. **Scope: a theorem about this sufficient-condition template, not a lower bound on all Euclidean constructions.**

## Statement

Suppose parameters \(m,L,s,a,C,K\) satisfy the finite criterion (C1), (C3), (C5) from Section 5 of the manuscript, with \(s>1\), \(0<a\le1\), \(L\ge3\), and
\[
 s^3\left(\frac12+\frac K{m^2}\right)\le \frac12+\varepsilon,\qquad \varepsilon>0.
\]
Then necessarily
\[
 \boxed{m>6\sqrt3\,\varepsilon^{-5/2}.}
\]

Consequently the *advertised ambient dimension* \(3m-1\) of this orthogonal-circle certificate grows at least on the order of \(\varepsilon^{-5/2}\) if one insists on obtaining the target coefficient using the criterion's own diameter upper bound. This does not assert that the constructed points have affine span exactly \(3m-1\), nor that alternative certificates/geometries cannot do better.

## Proof

The coefficient assumption implies \(s^3\le1+2\varepsilon\). Since \(s\ge1\),
\[
 3(s-1)\le s^3-1\le2\varepsilon,\qquad s-1\le 2\varepsilon/3.
\]

(C1) states \(\tau s(1-1/L)(1-a^2/8)>1\) with \(0<\tau<1\). Since each factor in parentheses is at most one, this implies separately
\[
 s(1-1/L)>1,\qquad s(1-a^2/8)>1.
\]
Thus
\[
 \frac1L<1-\frac1s\le s-1\le\frac{2\varepsilon}{3},
 \quad
 \frac{a^2}{8}<1-\frac1s\le\frac{2\varepsilon}{3}.
\]
In particular,
\[
 L>\frac3{2\varepsilon},\qquad a<\frac4{\sqrt3}\sqrt\varepsilon.
\]

By (C5), \(Ca\gamma>4L\), where \(\gamma=1-a^2/8\le1\). Therefore
\[
 C>\frac{4L}{a}>
 \frac{4(3/(2\varepsilon))}{(4/\sqrt3)\sqrt\varepsilon}
 =\frac{3\sqrt3}{2}\varepsilon^{-3/2}.
\]

The coefficient assumption also implies \(s^3K/m^2\le\varepsilon\). By (C3),
\[
 \frac{s^3K}{m^2}\ge\frac{4C}{m}.
\]
Consequently
\[
 \varepsilon\ge\frac{4C}{m}>
 \frac{6\sqrt3}{m}\varepsilon^{-3/2},
\]
which rearranges to \(m>6\sqrt3\,\varepsilon^{-5/2}\). QED.

## Interpretation

The companion near-counting family in
[FINITE670_SHARPENED_AND_NEAR_COUNTING_2026-10-16.md](FINITE670_SHARPENED_AND_NEAR_COUNTING_2026-10-16.md)
uses \(m=80r^5\) and a coefficient excess \(O(r^{-2})\), giving
\(m=O(\varepsilon^{-5/2})\). The exponent is therefore **optimal within the five-condition certificate when judged by its stated diameter bound**.

This identifies the next discovery seam: weaken or replace at least one of the interacting requirements (C1), (C3), (C5), or find a geometric architecture with different costs. Mere numerical parameter optimization of these same guards cannot beat the exponent.

No new Lean theorem, external review, or CI result is claimed.
