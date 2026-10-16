#!/usr/bin/env python3
"""Exact arithmetic and finite regressions for the smoothed triangular-wave discovery.

Uniform convolution and geometric proofs are in SMOOTHED_TRIANGULAR_WAVE_NEAR_COUNTING_2026-10-16.md.
No GitHub Actions, external libraries or Lean compilation are used.
"""
from fractions import Fraction as Q
from math import comb, sin, cos, pi, sqrt


def multiply(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def power(a, n):
    b = [Q(1)]
    for _ in range(n):
        b = multiply(b, a)
    return b


def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def evaluate(poly, u):
    return sum((c*u**i for i, c in enumerate(poly)), Q(0))


def universal_coefficient():
    u = [Q(1), Q(1)]
    main = multiply(power(u, 3), [Q(1, 2), Q(5, 12)])
    extra = [Q(0)]*4 + [c/Q(6144**2) for c in power(u, 2)]
    padding = power([Q(1), Q(0), Q(1, 6144)], 2)
    beta = multiply(add(main, extra), padding)
    assert beta[0] == Q(1, 2) and all(c >= 0 for c in beta[1:])
    gap = Q(1, 2) + Q(9, 4)*Q(1, 16) - evaluate(beta, Q(1, 16))
    assert gap > 0
    print("Universal endpoint exact gap:", gap, "~", float(gap))
    return beta


def check_instance(r, beta):
    assert r >= 16
    v = (16*r-1).bit_length()  # ceil(log_2(16r))
    D = 7*v
    modes = (D+1)//2
    m0 = 6144*r*r
    s = 1+Q(1, r)
    L = 4*r
    C = 320*r
    B = 2560*r
    K = B*m0
    tau0 = 1-Q(1)/(s*(K+1))
    gamma = 1-Q(1, 16*r)
    kappa = 1-Q(1, L)
    central_factor = Q(4**D, comb(2*D, D))
    tail = 2*(2*D+1)*Q(4, 5)**D
    assert tail < Q(1, 16*r), (r, D, tail)
    assert central_factor <= 2*D+1 and central_factor**2 >= D
    checks = {
        "H1 slope": tau0*s*kappa*gamma-1,
        "H2 harmonic offset": Q(B-512),
        "H3 flattening (amplitude < 2)": B*s**3-8*C,
        "H4 squared completion": Q(C*C*m0)-(84*s*s)**2*(B+1),
        "H5 local chord": Q(C)-64*L,
    }
    for name, margin in checks.items():
        assert margin > 0, (r, name, margin)
    coeff = (
        s**3*(Q(1, 2)+Q(B, m0)) + s*s/(2*tau0*m0*m0)
    ) * (1+Q(1, m0))**2
    upper = evaluate(beta, Q(1, r))
    target = Q(1, 2)+Q(9, 4*r)
    assert coeff < upper < target, (r, coeff, upper, target)
    dimension = 9216*(2*modes+1)*r*r-1
    print(
        f"r={r:<9} v={v:<3} D={D:<4} modes={modes:<4} "
        f"N={2*m0:<20} dimension={dimension:<28} "
        f"coeff={float(coeff):.12f} target={float(target):.12f}"
    )
    return D


def trig_regression(D):
    # Numerical diagnostic only; the uniform lower bound is proved in the note.
    cs = [
        (4/pi)*((-1)**((j-1)//2)) *
        (comb(2*D, D+j)/comb(2*D, D))/j**2
        for j in range(1, D+1, 2)
    ]
    amplitude = sum(abs(c) for c in cs)
    assert 1 < amplitude < 2 and cs[0] > 1

    def fprime(z):
        return sum(j*c*cos(j*z) for j, c in zip(range(1,D+1,2), cs))

    def square_sine(delta):
        return sum(j*abs(c)*sin(j*delta) for j,c in zip(range(1,D+1,2),cs))

    def chord(delta):
        return 2*sqrt(sum(
            abs(c)*amplitude*sin(j*delta/2)**2
            for j,c in zip(range(1,D+1,2),cs)
        ))

    min_chord_slope = float("inf")
    min_digit_derivative = float("inf")
    for i in range(1, 1001):
        delta = i/1000
        slope = amplitude*square_sine(delta)/chord(delta)
        min_chord_slope = min(min_chord_slope, slope)
        min_digit_derivative = min(min_digit_derivative, fprime(delta/2))
    assert min_chord_slope > 1/16
    assert min_digit_derivative > 0
    print(
        f"D={D}: amplitude={amplitude:.7f}; "
        f"sample min chord slope/R0={min_chord_slope:.6f}; "
        f"sample min digit derivative={min_digit_derivative:.6f}"
    )


if __name__ == "__main__":
    beta = universal_coefficient()
    degrees = set()
    for r in [16,17,31,32,33,64,100,256,1000,4096,65536,10**9]:
        degrees.add(check_instance(r,beta))
    for D in sorted(degrees):
        if D <= 154:
            trig_regression(D)
    print("PASS: exact sampled guards, universal polynomial, and finite trig regressions")
    print("General theorem requires the uniform proofs in the mathematical note.")
