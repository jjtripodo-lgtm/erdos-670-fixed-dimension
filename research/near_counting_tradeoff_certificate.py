#!/usr/bin/env python3
"""Exact arithmetic for near-counting Erdős 670 parameter tradeoffs.

No external dependencies, CI, Lean compiler, numerical approximation for
acceptance, or platform submissions. Universal deductions (including the
harmonic inequality, parameter inequalities, and calculus optimization)
are written in the accompanying research note. This checker supplies
exact rational endpoint and inequality certificates, plus sample regression.
"""
from fractions import Fraction as Q


def poly_mul(x, y):
    out = [Q(0)] * (len(x) + len(y) - 1)
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[i + j] += a * b
    return out


def poly_pow(x, n):
    out = [Q(1)]
    for _ in range(n):
        out = poly_mul(out, x)
    return out


def poly_add(x, y):
    out = [Q(0)] * max(len(x), len(y))
    for i, a in enumerate(x):
        out[i] += a
    for j, b in enumerate(y):
        out[j] += b
    return out


def evaluate(x, t):
    return sum((c * t**i for i, c in enumerate(x)), Q(0))


def strengthened_family():
    """Certify the exact rational endpoint for the improved universal family."""
    # t = 1/r^2; 0 < t <= 1/100. s=(1+13t/25),
    # kappa=(1-t/3), gamma=(1-9t/50).
    s_t = [Q(1), Q(13, 25)]
    kappa_t = [Q(1), Q(-1, 3)]
    gamma_t = [Q(1), Q(-9, 50)]
    product = poly_mul(poly_mul(s_t, kappa_t), gamma_t)
    assert product == [Q(1), Q(1, 150), Q(-388, 1875), Q(39, 1250)]
    # For 0<t<=1/100, drop the positive cubic and bound the
    # negative quadratic term by t/100 times its negative slope.
    digit_guard = Q(1, 150) - Q(388, 1875 * 100) - Q(1, 250)
    assert digit_guard > 0
    # K >= 3360 r^8: tau > 1-t/1000; combined with s*kappa*gamma
    # > 1+t/250, gives strict C1 on the entire parameter range.
    tau_guard = Q(1, 250) - Q(1, 1000) - Q(1, 250 * 1000 * 100)
    assert tau_guard > 0
    # C2 via H_m^2 < 2m (Cauchy-Schwarz and sum 1/k^2 < 2).
    assert 42 * 10**3 > 32768
    # C3: K = 4Cm and s>1; C4 follows from bounds s<101/100,
    # 84s^2<90 and K+m<=43r^3m, m>=80r^5.
    assert 84 * Q(101, 100)**2 < 90
    assert 8820 * 10**6 > 75**2 * 43
    # C5: C*a*gamma-4L=(3/5)r^2-567/250 >0.
    assert Q(3, 5) * 10**2 - Q(567, 250) > 0

    # u=1/r, m0=80r^5, B=42r^3. For m>=m0 and tau>1/2,
    # normalized diameter of the mk configuration is at most
    # s^3*(1/2 + 21u^2/40) + s^2*u^10/6400.
    # Deleting excess points multiplies the cap by (1+u^5/80)^2.
    s_u = [Q(1), Q(0), Q(13, 25)]
    core = poly_add(
        poly_mul(poly_pow(s_u, 3), [Q(1, 2), Q(0), Q(21, 40)]),
        [Q(0)] * 10 + [v / 6400 for v in poly_pow(s_u, 2)],
    )
    beta = poly_mul(core, poly_pow([Q(1)] + [Q(0)] * 4 + [Q(1, 80)], 2))
    assert beta[0] == Q(1, 2) and beta[1] == 0
    assert all(v >= 0 for v in beta[2:])
    # All powers beyond the constant are nonnegative, so
    # (beta(u)-1/2)/u^2 increases on [0, 1/10].
    umax = Q(1, 10)
    endpoint = evaluate(beta, umax)
    target = Q(1, 2) + Q(4, 3) * umax**2
    assert endpoint < target
    print('UNIFORM IMPROVED FAMILY: EXACT CERTIFICATES PASS')
    print('  digit polynomial:', product)
    print('  C1 digit guard:', digit_guard)
    print('  C1 slope guard:', tau_guard)
    print('  beta(1/10):', endpoint, '=', float(endpoint))
    print('  strict endpoint gap:', target - endpoint)
    print('  nonnegative polynomial terms beyond u^2:', len(beta) - 2)
    for r in (10, 11, 20, 100):
        s = 1 + Q(13, 25 * r**2)
        a, L = Q(6, 5 * r), 3 * r**2
        C, B, m0 = Q(21 * r**3, 2), 42 * r**3, 80 * r**5
        K = B * m0
        gamma = 1 - a*a/8
        kappa = 1 - Q(1, L)
        tau_lower = 1 - 1 / (s * (K + 1))
        assert tau_lower * s * kappa * gamma > 1
        assert B >= 32768
        assert B * s**3 > 4 * C
        assert C*C*m0 > (84*s*s/a)**2 * (B+1)
        assert C*a*gamma > 4*L
        u = Q(1, r)
        assert evaluate(beta, u) < Q(1, 2) + Q(4, 3) * u*u
        print('  sample r=%s: d=%s, n0=%s, beta=%.12f' % (
            r, 360*r**5-1, 160*r**5, float(evaluate(beta, u))))


def exponent_barrier():
    """Audit optimization algebra, not a floating-point search proof."""
    # For x = delta/epsilon in (0,2/3), maximize
    # x^(3/2)*(1-3x/2) by differentiating its square.
    # d/dx[x^3(1-3x/2)^2]
    # = 3x^2(1-3x/2)(1-5x/2), so the maximum is x=2/5.
    xmax = Q(2, 5)
    assert Q(1) - Q(3, 2) * xmax == xmax
    # [3sqrt(2)*(5/2)^(5/2)]^2 == [75sqrt(5)/4]^2.
    assert Q(18) * Q(5, 2)**5 == Q(75*75*5, 16)
    # In the certified sub-0.75 regime, C>12 and s^3<2,
    # hence 4C-s^3/2>3C. The other barriers follow from
    # C1, C3, C5 by algebra in the accompanying note.
    assert 4*12-1 > 3*12
    print('CERTIFICATE BARRIER: ALGEBRAIC OPTIMIZATION PASS')
    print('  maximizing delta/epsilon:', xmax)
    print('  m lower-bound constant: 75*sqrt(5)/4 ≈ 41.926274578...')
    print('  warning: applies to the FIVE-CONDITION CERTIFIED UPPER BOUND,')
    print('           not all constructions or improved geometric arguments.')


if __name__ == '__main__':
    strengthened_family()
    exponent_barrier()
