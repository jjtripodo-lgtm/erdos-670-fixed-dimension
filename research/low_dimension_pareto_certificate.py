#!/usr/bin/env python3
"""Exact rational certificates for Erdős 670 low-dimensional Pareto points.

No GitHub Actions, floating-point acceptance, or Lean replay. Each witness
instantiates the finite criterion in Section 5 of the manuscript.
"""
from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class Witness:
    name: str
    m0: int
    L: int
    s: Q
    a: Q
    C: Q
    K: int | None
    B: int | None
    tau_lower: Q
    cap: Q
    all_n: bool


WITNESSES = (
    Witness("infinite subsequence, 5801 dimensions", 1934, 19,
            Q(1081495, 1000000), Q(219, 500), Q(889, 5),
            1087364, None, Q(999999, 1000000), Q(1), False),
    Witness("all n >= 3878, 8723 dimensions", 1939, 19,
            Q(108175, 100000), Q(4401, 10000), Q(177),
            None, 561, Q(999999, 1000000), Q(1), True),
    Witness("all n >= 4000, 8999 dimensions", 2000, 19,
            Q(108311, 100000), Q(451, 1000), Q(173),
            None, 548, Q(999999, 1000000), Q(197, 200), True),
    Witness("all n >= 4400, 9899 dimensions", 2200, 18,
            Q(108677, 100000), Q(907, 2000), Q(163),
            None, 510, Q(999999, 1000000), Q(47, 50), True),
    Witness("all n >= 16000, 35999 dimensions", 8000, 20,
            Q(107827, 100000), Q(109, 250), Q(188),
            None, 600, Q(999999, 1000000), Q(361, 500), True),
    Witness("all n >= 20480, 46079 dimensions", 10240, 23,
            Q(2139, 2000), Q(53, 125), Q(222),
            None, 726, Q(999999, 1000000), Q(699, 1000), True),
)


def harmonic(m):
    # Exact rational finite sum, not an approximation to H_m.
    h = Q(0)
    for i in range(1, m + 1):
        h += Q(1, i)
    return h


def verify(w):
    m = w.m0
    assert m >= 4 and w.L >= 3
    assert w.s > 1 and 0 < w.a <= 1 and w.C > 0
    assert w.all_n == (w.B is not None)
    K = w.B * m if w.all_n else w.K
    assert K is not None and K > 0
    gamma = 1 - w.a*w.a/8
    lam = (1-Q(1, w.L))*gamma
    hm = harmonic(m)
    margins = {
        "derived tau > tau_lower": 1-w.tau_lower**2 - 1/(w.s*(K+1)),
        "C1 (fine digit)": w.tau_lower*w.s*lam-1,
        "C2 K >= m": Q(K-m),
        "C2 harmonic": Q(K)-16384*hm*hm,
        "C3 macro radius": Q(K)*w.s**3 - 4*w.C*m,
        "C4 squared": (w.C*m)**2-(84*w.s*w.s/w.a)**2*(K+m),
        "C5 local chords": w.C*w.a*gamma-4*w.L,
    }
    for name, val in margins.items():
        assert val > 0 or (name == "C2 K >= m" and val == 0), (w.name, name, val)
    if w.all_n:
        # H_m^2/m decreases for m >= 4, since H_m >= 2 and
        # (1+1/((m+1)H_m))^2 <= (1+1/(2(m+1)))^2 < 1+1/m.
        # Thus base C2 proves C2 for all m >= m0 when K=B*m.
        assert w.B >= 1
        assert w.B*w.s**3 >= 4*w.C
        # Squared C4 becomes C^2*m >= (84*s^2/a)^2*(B+1),
        # also monotone for m >= m0.
        assert w.C*w.C*m >= (84*w.s*w.s/w.a)**2*(w.B+1)
        # k=floor(n/m0), m=ceil(n/k), for n>=2m0.
        mmax = m + m//2
        dimension = 3*mmax - 1
        n_min = 2*m
        coefficient = (
            w.s**3 * (Q(1,2)+(Q(w.B)-Q(1,2))/m)
            + w.s*w.s/(2*w.tau_lower*m*m)
        ) * (1+Q(1,m))**2
    else:
        # Fixed m; n=m*k for every k>=2.
        dimension = 3*m - 1
        n_min = 2*m
        coefficient = (
            w.s**3 * (Q(K)+Q(m*(m-1),2))
            + w.s*w.s/(2*w.tau_lower)
        )/m**2
    assert coefficient < w.cap, (w.name, float(coefficient), w.cap)
    print("PASS:", w.name)
    print("  m0=%d, L=%d, s=%s, a=%s, C=%s, K=%s" % (
        w.m0, w.L, w.s, w.a, w.C,
        "B*m with B="+str(w.B) if w.all_n else str(w.K)))
    print("  dimension=%d, n_min=%d, beta=%.12f < cap=%s" % (
        dimension,n_min,float(coefficient),w.cap))
    print("  strict rational margin: %.12g (decimal display only)" %
          float(w.cap-coefficient))
    return dimension, n_min, coefficient


if __name__ == "__main__":
    results=[verify(w) for w in WITNESSES]
    assert results[0][0] == 5801
    assert [r[0] for r in results[1:]] == [8723,8999,9899,35999,46079]
    print("ALL SIX EXACT CERTIFICATES PASSED; no Lean verification claimed")
