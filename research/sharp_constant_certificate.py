#!/usr/bin/env python3
"""Exact rational audit for a near-optimal Erdős 670 certificate.

This checks polynomial signs, the universal rational endpoint and sample
C1-C5 witnesses. The universal inequalities and sharp limiting constant are
proved analytically in SHARP_LEADING_CONSTANT_2026-10-16.md.
No Lean replay or GitHub Actions.
"""
from fractions import Fraction as F
from math import sqrt


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def add(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def power(a, n):
    c = [F(1)]
    for _ in range(n):
        c = mul(c, a)
    return c


def value(a, u):
    return sum((x * u**i for i, x in enumerate(a)), F(0))


def polynomial_certificate():
    # For even r>=20, t=1/r^2 <= 1/400.
    slope = mul(
        mul([F(1), F(2, 5)], [F(1), -F(4, 15)]),
        [F(1), -F(10609, 80000)]
    )
    assert slope == [
        F(1), F(173, 240000), -F(74609, 600000), F(10609, 750000)
    ]
    assert slope[1] + slope[2] / 400 > F(1, 3000)
    assert (F(1) - F(1, 400)**4) * (F(1) + F(1, 1200000)) > 1

    # beta(u), u=1/r: strict upper bound after deletion and padding.
    s = [F(1), F(0), F(2, 5)]
    base = mul(power(s, 3), [F(1, 2), F(0), F(292, 735)])
    additive = [F(0)]*10 + [x / (147**2) for x in power(s, 2)]
    padding = [F(1), F(0), F(0), F(0), F(0), F(1, 147)]
    beta = mul(add(base, additive), power(padding, 2))
    assert beta[0] == F(1, 2) and beta[1] == 0
    assert all(x >= 0 for x in beta[2:])

    endpoint = value(beta, F(1, 20))
    assert endpoint == F(
        502119670754323832176983964812184340449,
        999247734374400000000000000000000000000,
    )
    assert endpoint < F(1, 2) + F(1, 400)
    print("EXACT POLYNOMIAL: PASS")
    print("beta(1/20):", endpoint, "=", float(endpoint))
    print("endpoint margin:", F(1, 2) + F(1, 400) - endpoint)
    optimum = 75 * sqrt(15) / 2
    print("sharp m0 leading constant:", optimum)
    print("explicit m0=147 overhead:", 147 / optimum - 1)
    return beta


def finite_regressions(beta):
    for r in (20, 22, 30, 50, 100, 200):
        t = F(1, r*r)
        m0 = 147*r**5
        s = 1 + F(2, 5)*t
        a = F(103, 100*r)
        L = 15*r*r//4
        C = F(73, 5)*r**3
        B = 4*C
        gamma = 1 - a*a/8
        lam = (1 - F(1, L))*gamma
        tau_lower = 1 - F(1)/(s*(B*m0 + 1))
        margins = {
            "C1": tau_lower*s*lam - 1,
            "C2 via H^2<2m": B - 32768,
            "C3": B*s**3 - 4*C,
            "C4 squared": C*C*m0 - (84*s*s/a)**2*(B+1),
            "C5": C*a*gamma - 4*L,
        }
        assert all(v > 0 for v in margins.values()), (r, margins)
        assert tau_lower > F(1, 2)
        assert value(beta, F(1, r)) < F(1, 2)+t
        print(f"r={r:3d} m0={m0} d={9*m0//2-1} "
              f"coefficient<{float(value(beta, F(1, r))):.12f}")
    print("EXACT SAMPLE WITNESSES: PASS (universal proof in the note)")


if __name__ == "__main__":
    finite_regressions(polynomial_certificate())
