# Sharp leading cluster-count constant in the Erdős 670 finite criterion

Research note, 16 October 2026. **Mathematical deduction from the manuscript's five-condition finite criterion, not an additional Lean-certified theorem or a universal dimension lower bound.** No GitHub Actions.

## Main theorem: constant optimality within this certificate

Let U(m,L,s,a,C,K) = [s³(K+m(m−1)/2)+s²/(2τ)]/m², where τ=√(1−1/[s(K+1)]), be the criterion's normalized diameter guarantee. For 0<ε<1/4 let m*(ε) be the minimum integer m≥4 admitting parameters satisfying C1–C5 and U<1/2+ε. The construction below shows this set is nonempty for sufficiently small ε.

**Theorem.**

\[
\lim_{\varepsilon\downarrow0}\varepsilon^{5/2}m_*(\varepsilon)
=\frac{75\sqrt{15}}2=145.23687548\ldots.
\]

This is an optimal leading constant for the *specific five-condition sufficient certificate and its stated upper diameter bound*, not for all geometric configurations or every alternative analysis of these points.

### Lower bound

Put δ=s−1 and γ=1−a²/8. Since τ<1, C1 implies s(1−1/L)γ>1. Consequently δ−sa²/8>0 and

\[
L>\frac{s\gamma}{s\gamma-1}.
\]

By C5,

\[
C>\frac{4L}{a\gamma}>\frac{4s}{a(\delta-sa^2/8)}.
\]

Maximizing a(δ−sa²/8) over all positive a gives its maximum at a²=8δ/(3s), with value (2δ/3)√(8δ/(3s)). Therefore

\[
C>3\sqrt{3/2}\,s^{3/2}\delta^{-3/2}. \tag{1}
\]

We also have C>12 from C5, L≥3, a≤1, γ≤1. As m≥4 and U<1/2+ε≤3/4, the positive terms of U give s³<2. By C3,

\[
U\ge \frac{s^3}{2}+\frac{4C-s^3/2}{m}.
\]

The second numerator is positive because C>12 and s³<2. Therefore s³<1+2ε, implying 0<δ<2ε/3. Combining the preceding displays with s³≥1+3δ gives

\[
m>
\frac{12\sqrt{3/2}\,s^{3/2}\delta^{-3/2}-s^3/2}
{\varepsilon-3\delta/2}.
\]

Because δ=O(ε), the subtracted term is uniformly negligible compared with δ^(−3/2). Write x=δ/ε∈(0,2/3). The function x^(3/2)(1−3x/2) is maximized at x=2/5, with maximum (2/5)^(5/2). Thus

\[
\liminf_{\varepsilon\downarrow0}\varepsilon^{5/2}m_*(\varepsilon)
\ge12\sqrt{3/2}(5/2)^{5/2}
=\frac{75\sqrt{15}}2.
\]

### Matching upper bound

For any fixed η>0 and all sufficiently small ε>0, set

\[
s=1+2\varepsilon/5,\quad
a=4\sqrt{\varepsilon/(15s)},\quad
L=\lceil15/(4\varepsilon)\rceil+2,\quad
\gamma=1-a^2/8,
\]
\[
C=(1+\varepsilon)\frac{4L}{a\gamma},\quad
m=\left\lceil(75\sqrt{15}/2+\eta)\varepsilon^{-5/2}\right\rceil,
\quad K=4Cm/s^3.
\]

Here sγ=1+4ε/15. With A=15/(4ε), one has L≥A+2 and

\[
s(1-1/L)\gamma\ge (A+1)^2/[A(A+2)]
=1+1/[A(A+2)]=1+\Theta(\varepsilon^2).
\]

Meanwhile K=Θ(ε^(−4)), so 1−τ=O(ε^4), establishing C1. C3 holds with equality; C5 holds strictly. Using H_m²<2m, C2 follows since K/m=Θ(ε^(−3/2)). C4 follows because (Cm)²=Θ(ε^(−8)), whereas (84s²/a)²(K+m)=Θ(ε^(−5)).

Finally,

\[
C=(15\sqrt{15}/4+o(1))\varepsilon^{-3/2}
\]

and

\[
U=\frac12+\left[\frac35+
\frac{15\sqrt{15}}{75\sqrt{15}/2+\eta}\right]\varepsilon
+o(\varepsilon)<\frac12+\varepsilon.
\]

Taking η arbitrarily small proves the matching limsup and the theorem.

For arbitrary n≥2m₀ with m₀ equal to this initial m, use k=floor(n/m₀), m'=ceil(n/k), and the same parameter scheme with K=4Cm'/s³. Then m₀≤m'≤ceil(3m₀/2); deletion and coordinate padding give dimension at most 3ceil(3m₀/2)−1, and relative rounding overhead O(1/m₀)=o(ε). The sharp leading cluster-count constant therefore also applies to this all-n certificate family, although the padded dimension includes its extra factor of approximately 3/2.

## Entirely rational explicit witness within 1.22% of optimal cluster count

For every **even integer r≥20**, set m₀=147r⁵, and for every integer m≥m₀ use

\[
s=1+\frac2{5r^2},\quad a=\frac{103}{100r},\quad
L=\frac{15r^2}{4},\quad C=\frac{73}{5}r^3,\quad
K=\frac{292}{5}r^3m.
\]

**Corollary.** For every even r≥20 and every integer n≥294r⁵, the finite criterion gives a distance-separated n-point configuration in

\[
\mathbb R^{(1323/2)r^5-1}
\]

with diameter strictly below (1/2+1/r²)n².

**Proof.** Put t=1/r²≤1/400, κ=1−4t/15, γ=1−10609t/80000. Multiplication gives

\[
s\kappa\gamma=1+\frac{173}{240000}t
-\frac{74609}{600000}t^2+\frac{10609}{750000}t^3
>1+t/3000.
\]

Also K≥(42924/5)r⁸, so τ=√(1−1/[s(K+1)])>1−t⁴. Since (1−t⁴)(1+t/3000)>1 for t≤1/400, C1 holds.

For C2, Cauchy–Schwarz and Σ_{j≥1}j⁻²<2 imply H_m²<2m. Since K/m=(292/5)r³>32768, K≥max(m,16384H_m²). C3 follows from K=4Cm>4Cm/s³. For C4, 84s²/a<100r and K+m<60r³m; its squared right side is <600000r⁵m, while (Cm)²≥(5329·147/25)r¹¹m>600000r⁵m. C5 is

\[
Ca\gamma-4L=\frac{19}{500}r^2-
\frac{7519\cdot10609}{500\cdot80000}>0.
\]

The criterion therefore applies to all m≥m₀ and k≥2. For n≥2m₀ use k=floor(n/m₀), m=ceil(n/k), delete extra points, and pad. Because m₀ is even, m≤3m₀/2 and n≤mk<(1+1/m₀)n.

With u=1/r, since τ>1/2, the normalized final diameter is strictly below

\[
\beta(u)=\left[(1+2u^2/5)^3(1/2+292u^2/735)
 +(1+2u^2/5)^2u^{10}/147^2\right](1+u^5/147)^2.
\]

Every coefficient of β(u)−1/2 is nonnegative, so (β(u)−1/2)/u² is increasing for u>0. Exact rational arithmetic establishes

\[
\beta(1/20)=
\frac{502119670754323832176983964812184340449}
{999247734374400000000000000000000000000}
<\frac12+\frac1{400}.
\]

Thus β(1/r)<1/2+1/r² for all even r≥20. QED.

The explicit m₀=147r⁵ is only 147/(75√15/2)−1≈1.214% above the proved asymptotic optimum **for this certificate**. Dimensions and starting n are very large.

## Reproduction and implications

Run the pure-standard-library companion research/sharp_constant_certificate.py. It checks the rational polynomials, exact endpoint margin, and several representative C1–C5 instances. The universal quantifiers and asymptotic theorem come from the analytic arguments above, not samples.

The existing hardcoded Lean endpoint proves the older 0.735 statement; it has not been changed. Improving either the exponent 5/2 or the leading constant inside this particular certificate is impossible. The open discovery direction is a geometric redesign or a stronger inequality replacing C1/C3/C5 or the stated diameter estimate.
