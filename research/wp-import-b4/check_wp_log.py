#!/usr/bin/env python3
"""Fail closed on unresolved B002-B4 WP goals."""
import re,sys,json
from pathlib import Path
s=Path(sys.argv[1]).read_text(errors="replace")
summaries=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",s)
assert len(summaries)==1,summaries
p,t=map(int,summaries[0])
assert (p,t)==(22,22),f"Expected 22/22, got {p}/{t}"
assert not re.search(r"\[Timeout\]|returns (?:Timeout|Unknown|Failed)|\[wp\]\s+\[Failed\]",s),"Unresolved goal"
assert "Alt-Ergo 2.6.4" in s and "Prover Alt-Ergo 2.5.4" not in s
def check(name):
    m=re.search(r"(?m)^Goal "+re.escape(name)+r"[^\n]*:",s)
    assert m, name+" missing"
    rest=s[m.end():];end=re.search(r"\n-{8,}\s*\n",rest)
    assert end, name+" missing section end"
    section=rest[:end.start()]
    assert re.search(r"Prover (?:Alt-Ergo 2\.6\.4|Qed) returns Valid",section),name+" not Valid"
for name in (
 "Lemma 'b002b1_decoded_euler'","Lemma 'b002b2_finite_euler'",
 "Lemma 'b002b3_lower_bound'","Lemma 'b002b3_upper_bound'",
 "Lemma 'b002b3_first_range'","Lemma 'b002b4_second_lower'",
 "Lemma 'b002b4_second_upper'","Lemma 'b002b4_second_range'",
 "Post-condition 'decoded_update' in 'compare_update'",
 "Post-condition 'finite_update' in 'compare_update'"
):check(name)
for name in ("imported_decoded_euler","imported_finite_euler","imported_first_range","imported_second_range"):
    assert "Pre-condition '"+name+"'" not in s
result={"experiment":"B002-B4","status":"SECOND_RANGE_AND_COMPOSITION_PROVED_WITHIN_WP","proved":p,"total":t,"remaining_imports":["imported_decoded_average","imported_finite_average"],"scope":"ACSL/WP model only; no C runtime to Lean semantics"}
print(json.dumps(result,indent=2))
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+"\n")
