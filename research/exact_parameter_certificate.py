#!/usr/bin/env python3
"""Exact rational certificates for the 2026-10-16 Erdos 670 discovery.

Verifies the finite-parameter witness and the rational polynomial endpoint
used by the universal near-counting-bound family. Standard library only.
Uniform harmonic and symbolic inequalities are proved in the companion note;
sampling integer r is NOT a universal proof.
"""
from fractions import Fraction as Q


def check_finite():
    m0, L, C, B = 18177, 28, 305, 1037
    s, a, tau_lower = Q(10557, 10000), Q(3, 8), Q(99999, 100000)
    gamma = 1 - a * a / 8
    lam = (1 - Q(1, L)) * gamma
    margins = {
        "slope tolerance": 1 - tau_lower**2 - 1 / (s * (B*m0 + 1)),
        "C1 fine digit": tau_lower*s*lam - 1,
        "C2 harmonic via H_m0 <= 16": B*m0 - 16384*16**2,
        "C3 macro offset": B*s**3 - 4*C,
        "C4 squared radius": Q(C*C*m0) - (84*s*s/a)**2*(B+1),
        "C5 local chords": Q(C)*a*gamma - 4*L,
    }
    assert all(x > 0 for x in margins.values()), margins
    # H_m^2/m is nonincreasing for m >= 4 (proved in the note),
    # so the base C2 check covers all m >= m0. All other guards
    # are monotone under K=Bm and K+m=(B+1)m.
    padded = (
        s**3 * (Q(1, 2) + (Q(B)-Q(1, 2))/m0)
        + s*s/(2*tau_lower*m0*m0)
    ) * (1 + Q(1, m0))**2
    assert padded < Q(82, 125)
    print("FINITE: PASS")
    for name, value in margins.items():
        print("  %-33s %s" % (name, value))
    print("  padded coefficient             ", padded, "=", float(padded))
    print("  strict bound                  < 82/125 = 0.656")
    return padded


def polynomial_multiply(a, b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def polynomial_power(a, n):
    out = [Q(1)]
    for _ in range(n):
        out = polynomial_multiply(out, a)
    return out


def poly_evaluate(coeffs, t):
    return sum((c*t**i for i, c in enumerate(coeffs)), Q(0))


def check_family():
    # u=1/r; m0=80*r^5, B/m0=u^2, 1/m0=u^5/80.
    # beta(u)=((1+u^2)^3*(1/2+u^2)
    #          +(1+u^2)^2*u^10/6400)*(1+u^5/80)^2.
    u2 = [Q(1), Q(0), Q(1)]
    u5 = [Q(1)] + [Q(0)]*4 + [Q(1, 80)]
    term1 = polynomial_multiply(polynomial_power(u2, 3), [Q(1, 2), Q(0), Q(1)])
    term2 = [Q(0)]*10 + [x/Q(6400) for x in polynomial_power(u2, 2)]
    summed = [Q(0)]*max(len(term1), len(term2))
    for j, value in enumerate(term1):
        summed[j] += value
    for j, value in enumerate(term2):
        summed[j] += value
    coeffs = polynomial_multiply(summed, polynomial_power(u5, 2))
    assert coeffs[0] == Q(1, 2) and coeffs[1] == 0
    assert all(c >= 0 for c in coeffs[2:])
    # Hence (beta(u)-1/2)/u^2 is nondecreasing for u >= 0.
    umax = Q(1, 10)
    beta10 = poly_evaluate(coeffs, umax)
    target10 = Q(1, 2) + Q(13, 5)*umax**2
    assert beta10 < target10
    print("FAMILY: PASS universal endpoint polynomial certificate")
    print("  beta(1/10)                  =", float(beta10))
    print("  target at 1/10             =", float(target10))
    print("  rational endpoint gap      =", target10-beta10)
    print("  positive higher-degree terms=", sum(c > 0 for c in coeffs[2:]))

    # Sample checks are regression tests, not the universal proof.
    for r in [10, 11, 20, 30, 100]:
        m0, L = 80*r**5, 4*r**2
        s, a, C, B = 1 + Q(1,r*r), Q(1,r), 20*r**3, 80*r**3
        gamma = 1-a*a/8
        lam = (1-Q(1,L))*gamma
        K = B*m0
        tau_lower = 1-Q(1)/(s*(K+1))
        assert tau_lower*s*lam > 1
        assert B >= 65536
        assert B*s**3 >= 4*C
        assert C*C*m0 >= (84*s*s/a)**2*(B+1)
        assert C*a*gamma > 4*L
        u=Q(1,r)
        assert poly_evaluate(coeffs,u) < Q(1,2)+Q(13,5)*u*u
        print("  r=%-4d  dimension=%-14d n_min=%-14d coefficient_cap=%.9f" % (
            r, 360*r**5-1, 160*r**5, float(poly_evaluate(coeffs,u))))


if __name__ == "__main__":
    check_finite()
    check_family()
