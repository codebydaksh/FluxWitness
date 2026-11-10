#!/usr/bin/env python3
"""Fail-closed WP goal audit for 2 split bounds and the original range theorem."""
import re,sys,json
from pathlib import Path
s=Path(sys.argv[1]).read_text(errors="replace")
summary=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",s)
assert len(summary)==1,summary
p,t=map(int,summary[0])
assert (p,t)==(19,19),f"Need 19/19, saw {p}/{t}"
assert not re.search(r"\[Timeout\]|returns (?:Timeout|Unknown|Failed)|\[wp\] \[Failed\]",s), "Unresolved WP goal"
assert "Alt-Ergo 2.6.4" in s and "Prover Alt-Ergo 2.5.4" not in s
def valid(title):
    m=re.search(r"(?m)^Goal "+re.escape(title)+r"[^\n]*:",s)
    assert m, title+" missing"
    tail=s[m.end():]
    end=re.search(r"\n-{8,}\s*\n",tail)
    assert end, title+" section lacks separator"
    section=tail[:end.start()]
    assert re.search(r"Prover (?:Alt-Ergo 2\.6\.4|Qed) returns Valid",section), title+" not Valid"
for goal in ("Lemma 'b002b1_decoded_euler'",
             "Lemma 'b002b2_finite_euler'",
             "Lemma 'b002b3_lower_bound'",
             "Lemma 'b002b3_upper_bound'",
             "Lemma 'b002b3_first_range'",
             "Post-condition 'decoded_update' in 'compare_update'",
             "Post-condition 'finite_update' in 'compare_update'"):
    valid(goal)
assert "Pre-condition 'imported_first_range'" not in s
assert "Pre-condition 'imported_decoded_euler'" not in s
assert "Pre-condition 'imported_finite_euler'" not in s
result={"experiment":"B002-B3 split","status":"PROVED_WP_SUBGOALS_ONLY",
        "proved":p,"total":t,"imported_caller_premises_remaining":3,
        "note":"WP relative to ACSL/Why3 semantics; C/Lean mapping still open"}
print(json.dumps(result,indent=2))
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+"\n")
