"""Exact scalar audit for the finite paper.

The m-universal assertions use the monotonicity reductions in the TeX.
This is not a geometric proof, Lean replay, or specialist review.
"""

from fractions import Fraction as Q


def require(name, condition):
    if not condition:
        raise ValueError(f"finite scalar check failed: {name}")


def positive(name, value):
    require(name, value > 0)
    print(f"{name}: {value} > 0")


# The harmonic guard alone gives K >= 16384 H_m^2 >= 16384 > 10.
require("harmonic cutoff", 16384 > 10)

# Finite family, universally for integer m >= m0.
m0, B, L, C = 18177, 284, 12, 101
s, a, tau = Q(9, 8), Q(49, 100), Q(9999, 10000)
kappa, gamma = 1 - Q(1, L), 1 - a * a / 8
lam = kappa * gamma
require("derived gamma and lambda", gamma == Q(77599, 80000) and lam == Q(853589, 960000))
positive("C1", tau * s * lam - 1)

# H_m0 <= 16 by dyadic blocks; H_{m+1}-H_m <= 1/1100.
positive("harmonic base", Q(m0, 1100) - 16)
require("harmonic induction step", Q(1, m0 + 1) <= Q(1, 1100))
# (m-1)/64 is increasing; (m-1)/m is increasing.
require("offset base", Q(m0 - 1, 64) == B)
positive("C2 harmonic K margin", Q(m0 - 1, 64 * m0) - Q(16384, 1100**2))
# m^2-3969m-4032 increases for m >= m0.
positive("K+m upper polynomial", m0**2 - 3969 * m0 - 4032)
require("K+m polynomial monotonicity", 2 * m0 - 3969 > 0)
positive("C3", B - 4 * C / s**3)
positive("C4 squared against 28", Q(28**2 * 63) - (84 * s**2 / a) ** 2)
require("radius constant above 28", 28 < C)
positive("C5", C * a * gamma / (4 * L) - 1)
# The derived tau is sqrt(1-x), x=1/[s(K+1)]. The rational tau here is
# only a lower bound; x decreases as m increases.
positive("derived tau above finite rational bound",
         1 - tau**2 - 1 / (s * (B * m0 + 1)))
# (s^3 B-Ca)m-1 increases for m >= m0.
# The former (C7) is universally implied by (C3) and (C5):
# s^3*K >= 4*C*m, while Ca*gamma > 4L >= 12, a<=1 and gamma<=1
# imply (4-a)*Cm >= 3Cm > 36 > 1.
require("automatic local-cross hypotheses", L >= 3 and 0 < a <= 1 and 0 < gamma <= 1)
positive("automatic local-cross guard, finite instance", s**3 * B - C * a - Q(1, m0))

c = s**3 * Q(33, 64)
overhead = s**3 + s**2 / (2 * tau)
require("leading coefficient", c == Q(24057, 32768))
positive("finite-diameter reduction", 4 * c - overhead)
mmax = m0 + (m0 - 1 + 1) // 2
require("maximum m and dimension", mmax == 27265 and 3 * mmax - 1 == 81794)
require("n threshold", 2 * m0 == 36354)
padded = c * Q(m0 + 1, m0) ** 2
require("padded coefficient identity", padded == Q(220816318833, 300740452352))
positive("all-n coefficient below 147/200", Q(147, 200) - padded)

# Direct deletion of old (C6) would be false: all other old assumptions
# hold at this rational tuple while its slope-budget inequality fails.
bad_tau = 1 - Q(1, 10**12)
K0 = (m0 * (m0 - 1) + 63) // 64
require("counterexample offset", K0 == B * m0)
require("counterexample C1", bad_tau * s * lam > 1)
require("counterexample C2 base", K0 >= max(10, m0))
require("counterexample C2 harmonic", Q(K0) >= Q(16384 * m0**2, 1100**2))
require("counterexample C3", Q(K0) >= 4 * C * m0 / s**3)
require("counterexample C4", (C * m0) ** 2 >= (84 * s**2 / a) ** 2 * (K0 + m0))
require("counterexample C5", C * a * gamma > 4 * L)
positive("counterexample: direct old C6 deletion fails",
         1 / (s * (K0 + 1)) - (1 - bad_tau**2))

print("PASS: finite five-condition criterion, cutoff and exact all-n margins")
