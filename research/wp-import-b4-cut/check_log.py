#!/usr/bin/env python3
"""Assess only the new stencil lemma; never claim the other two failures closed."""
from pathlib import Path
import re,sys,json
s=Path(sys.argv[1]).read_text(errors="replace")
totals=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",s)
assert len(totals)==1,totals
p,t=map(int,totals[0])
assert t==23, f"Unexpected proof inventory: {p}/{t}"
name="Lemma 'b002b4_stencil_range'"
m=re.search(r"(?m)^Goal "+re.escape(name)+r"[^\n]*:\s*$",s)
assert m,"Stencil goal missing"
tail=s[m.end():]
end=re.search(r"\n-{8,}\s*\n",tail)
assert end,"Stencil goal not delimited"
section=tail[:end.start()]
outcome="Valid" if re.search(r"Prover (?:Alt-Ergo 2\.6\.4|Qed) returns Valid",section) else "NOT_VALID"
other={}
for name in ("b002b4_second_lower","b002b4_second_upper","b002b4_second_range"):
    q=re.search(r"(?m)^Goal Lemma '"+name+r"':\s*$",s)
    assert q,name+" goal missing"
    sec=s[q.end():];boundary=re.search(r"\n-{8,}\s*\n",sec)
    assert boundary
    sec=sec[:boundary.start()]
    other[name]="Valid" if "returns Valid" in sec else "UNRESOLVED"
result={"experiment":"B002-B4 stencil cut","stencil":outcome,
        "wp_goals":f"{p}/{t}","second_stage_goals":other,
        "scope":"Diagnostic only; no imported premise discharged unless all WP goals independently valid"}
print(json.dumps(result,indent=2))
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+"\n")
assert outcome=="Valid","New stencil lemma not discharged"
