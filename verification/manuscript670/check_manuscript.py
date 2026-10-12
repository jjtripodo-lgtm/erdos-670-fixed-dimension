#!/usr/bin/env python3
"""Supplementary exact arithmetic and TeX-reference checks, not a Lean replay."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("paper/fixed_dimension_670.tex")
data = source.read_bytes()
text = data.decode("utf-8")
s = F(9, 8)
m0 = 34000
K0 = F(m0 * (m0 - 1), 64)
g = s * F(255, 256)
checks = {}

def check(name, condition):
    checks[name] = bool(condition)
    if not condition:
        raise SystemExit("FAIL: " + name)

check("K0", K0 == F(72247875, 4))
check("harmonic_base", F(m0, 2000) == 17)
check("harmonic_quadratic_bound", F(16384, 2000**2) <= F(m0 - 1, 64*m0))
check("K_ge_500m", F(m0 - 1, 64) >= 500)
# m^2 - 3969m - 4032 >= 0 follows from m^2 >= 34000m.
check("offset_plus_m_bound", (m0 - 3969)*m0 >= 4032)
check("flattening", F(35000)/s**6 <= F((m0-1)**2, 64**2*16))
check("first_harmonic_reserve", F(21168*32, 63)*s**4 == F(137781, 8))
check("total_reserve", F(1944,25)+F(137781,8) < 17500)
check("slope_reserve", (F(137781,8)+F(3888,25))/32 < 600)
check("radius_lower", 96**2 <= 17500)
check("radius_upper", 17500 <= 133**2)
check("cosine_lower", 1-F(1,32) >= F(9,10))
check("local_slope", F(600,225) < 3 and 3*F(9,10)/2 > 1)
check("minimum_baseline", s**3*(K0+1)-F(117,128) > 25000000)
check("error_coefficient", 2*s**3/F(25000000) < F(1,10**6))
check("amplitude_plus_error", F(117,128)+F(1,2*10**6) <= 1)
check("fine_coefficient", g > F(11,10))
check("fine_secondary_term", g*s/4 <= 1)
check("fine_guard", (g-1)*25000000 >= 2)
check("carry_guard", s*(g-1) >= F(2,10**6))
check("macro_guard", s >= 1 and s**3-s**2 >= 0 and s*(s-1) >= F(2,10**6))
check("mixed_guard", s**3*500 >= 700 and 700*m0-1 >= 600*m0)
finite = s**3*(F(1,63)+F(1,2))+F(1,m0*m0)
rounded = F(147,200)*F(34001,34000)**2
check("finite_diameter", finite < F(147,200))
check("rounded_diameter", rounded < F(37,50))
check("fixed_dimension", 9*51000-1 == 458999)
check("short_gram_coefficient", 754 < 1024)
check("zero_vector_nonstrict_gram_display", bool(re.search(
    r"\\frac\{\\sqrt\{754\}\}\{64\}\\,\\mathsf Q\[x\]\s*\\le\\tfrac12\\mathsf Q\[x\]",
    text)) and "At $x=0$ all forms vanish" in text)
# For k >= 2, (64/9) + 9k^2 <= 18k^2; the difference grows with k.
check("whole_B_extraction_coefficient", F(64,9) <= 9 * 2**2)
# K+m < m^2/36 and the whole-solve factor is 12*18=216.
check("whole_B_budget", 216 // 6 == 36 and 3*36**2 == 3888)
check("local_derivative_domain_stated", r"9p\delta\le d\le Y" in text)
labels = re.findall(r"\\label\{([^}]+)\}",text)
refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}",text)
keys = re.findall(r"\\bibitem\{([^}]+)\}",text)
cites = [k for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}",text) for k in group.split(',')]
check("unique_labels",len(labels)==len(set(labels)))
check("resolved_references",set(refs)<=set(labels))
check("resolved_citations",set(cites)<=set(keys))
check("balanced_braces",text.count('{')==text.count('}'))
print(json.dumps({"scope":"supplementary exact rational comparisons and TeX source checks; not full proof validation", "source_sha256":hashlib.sha256(data).hexdigest(),"check_count":len(checks),"checks":checks,"finite_coefficient":str(finite),"rounded_coefficient":str(rounded)},indent=2,sort_keys=True))
