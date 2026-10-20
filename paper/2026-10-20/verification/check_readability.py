"""Scoped exact controls for the readability revision; not a Lean replay."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parents[1]
normal = subprocess.check_output(["python3", str(root / "certificate_reconstruction.py")])
optimized = subprocess.check_output(["python3", "-O", str(root / "certificate_reconstruction.py")])
if normal != optimized:
    raise ValueError("optimization mismatch")
new = json.loads(normal)
old = json.loads((root / "verification/r29/EXACT_RECEIPT.json").read_text())
for row, matrix in zip(old["matrix_rows"], new["matrices"].values()):
    encoded = json.dumps(matrix["pivots"], sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(encoded).hexdigest() != row["pivots_sha256"]:
        raise ValueError(row["name"])

# Rational lower bounds for the displayed estimates over 0 < xi <= 1/8.
# Their derivations are in Sections 4.1, 4.3 and 4.5; no sampling in xi.
x = F(1, 8)
checks = {
    "completion_norm_squared_slack": F(128)**2 - F(84)**2 * F(9, 8)**5,
    "epsilon_digit_slack_per_xi_lower": F(3, 4) - F(15, 64)*x,
    "cubic_scale_slack_per_xi_lower": 1 - 3*x - x*x,
    "dyadic_base_at_r13": F(2)**13/F(16) - F(15)**2,
    "dyadic_induction_at_r13": F(13)**2 + 2*F(13) - 1,
    "shortening_gate_per_m": F(256)**2 - 2*F(128)**2,
    "digit_to_ruler_ratio_squared_slack": 1 - F(144, 49)*x,
    "local_slope_squared_slack": F(28, 3)**2/(1 + F(144, 49)*x) - 1,
    "coefficient_rounding_per_xi_slack": 1 - F(2, 1024) - x/F(1024)**2,
    "small_term_absorption_per_xi_slack": F(1, 2) - 3*x/F(1024)**2,
}
if any(v <= 0 for v in checks.values()):
    raise ValueError(checks)

# Finite regression controls for the shared ruler lemma. Its universal
# statement is established by the written modular argument, not this loop.
def prime(p):
    return p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1))

cases = 0
for m in range(2, 8):
    for k in range(2, 12):
        p = next(q for q in range(m*k + 1, 2*m*k + 1) if prime(q))
        for L in (2, 3):
            marks = [[L*p*i + (i*i + 2*k*A*i) % p for i in range(k)]
                     for A in range(m)]
            pairs = [(marks[A][j] - marks[A][i], j-i)
                     for A in range(m) for i in range(k) for j in range(i+1, k)]
            if len({g for g, d in pairs}) != len(pairs):
                raise ValueError(("collision", m, k, L))
            last = 0
            for g, d in sorted(pairs):
                if not ((L*d-1)*p < g < (L*d+1)*p and d >= last):
                    raise ValueError("lag order")
                last = d
            cases += 1

readset = json.loads((root / "SOURCE_READSET.json").read_text())
for key, row in readset.items():
    data = (root / row["retained_file"]).read_bytes()
    git_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if git_blob != row["git_blob"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
        raise ValueError(("source", key))
if F(999,1000)-F(499,500)*(1+F(5,400000))**2 <= 0:
    raise ValueError("all-n padding")
record = {
    "status": "PASS_SCOPED_REVIEW_CONTROLS",
    "source_pivots_matched": 15,
    "matrices": 3,
    "scalar_guards": len(new["positive_scalar_margins"]),
    "normal_optimized_identical": True,
    "universal_epsilon_estimate_lower_bounds": {k: str(v) for k, v in checks.items()},
    "finite_ruler_regression_cases": cases,
    "frozen_source_identities_matched": len(readset),
    "all_n_padding_margin": str(F(999,1000)-F(499,500)*(1+F(5,400000))**2),
    "scope": "Exact arithmetic controls and finite regression checks accompany the written proof review; no new Lean execution or independent proof review.",
}
out = json.dumps(record, indent=2) + "\n"
(root / "verification/READABILITY_AUDIT.json").write_text(out)
print(out, end="")
