#!/usr/bin/env python3
from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[1]
text=(root/'verification/axioms.log').read_text()
found={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
expected=['Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670']+['Erdos670Bridge.'+n for n in ['hasSeparatedDistances_image','finite_counterexample','not_fixedDimensionStatement','erdos_670_negated']]
assert set(found)==set(expected)
assert all(v==['propext','Classical.choice','Quot.sound'] for v in found.values())
print('PASS: original endpoint and four adapter endpoints have only propext, Classical.choice, Quot.sound (transitive axiom report)')
