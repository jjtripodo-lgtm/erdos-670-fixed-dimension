#!/usr/bin/env python3
"""Structural size/prime/gap audit for the #670 R29 research-status addendum.

This deliberately does NOT prove the Euclidean construction or certify the
inherited all-size analytic tail, Gram/Schur positivity, or Lean theorems.
Use only as a narrow exact arithmetic/provenance sanity check.
"""
from fractions import Fraction
from math import isqrt
import json

SMALL = ((43, 263, 5), (44, 269, 6), (45, 271, 6),
         (46, 277, 6), (47, 283, 6), (48, 293, 5),
         (49, 307, 5))
NEXT = ((50, 307, 6), (51, 307, 6),
        (52, 313, 7), (53, 331, 5))


def is_prime(x):
    return x >= 2 and all(x % d for d in range(2, isqrt(x) + 1))


def check_windows(windows, lo, hi):
    seen = set()
    for k, p, rmax in windows:
        assert p > 6 * k and is_prime(p)
        assert all(not is_prime(candidate) for candidate in range(6 * k + 1, p))
        assert rmax >= 0 and rmax < k
        seen.update(6 * k - r for r in range(rmax + 1))
    expected = set(range(lo, hi + 1))
    assert seen == expected, {
        "missing": sorted(expected - seen), "excess": sorted(seen - expected)
    }
    return sorted(seen)


def main():
    small = check_windows(SMALL, 253, 294)
    next_window = check_windows(NEXT, 294, 318)
    assert set(small).intersection(next_window) == {294}
    assert set(small).union(next_window) == set(range(253, 319))
    assert list(range(283, 289)) == [6 * 48 - r for r in range(5, -1, -1)]
    assert 5 + 6 + 6 + 6 + 6 == 29
    assert 288 * 287 // 2 == 41_328
    scale = Fraction(2_000_000, 2_095_999)
    raw_gap = Fraction(131, 125)
    epsilon = Fraction(1, 10_000_000)
    margin = scale * raw_gap - 1 - 4 * epsilon
    assert margin == Fraction(404_001, 5_239_997_500_000) and margin > 0
    out = {
        "scope": "STRUCTURAL_ONLY_NOT_A_GEOMETRY_OR_LEAN_PROOF",
        "dimension": 29,
        "finite_small_window": [small[0], small[-1]],
        "finite_next_window": [next_window[0], next_window[-1]],
        "finite_union": [253, 318],
        "formal_B48_size_interval_reported_in_private_source": [283, 288],
        "raw_288_unordered_edge_count": 41_328,
        "positive_exact_perturbation_margin": str(margin),
        "infinite_tail_geometry_Gram_and_Lean_proof": "NOT_CHECKED"
    }
    print(json.dumps(out, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
