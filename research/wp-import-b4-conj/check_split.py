#!/usr/bin/env python3
"""Fail-closed WP 32.1 conjunction-splitting diagnostic, no source changes."""
import json,re,sys
from pathlib import Path
log=Path(sys.argv[1]).read_text(errors="replace")
m=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",log)
assert len(m)==1,f"Unexpected proof summaries: {m}"
p,t=map(int,m[0])
assert t>=3, f"Expected stage assertions to generate goals, got {p}/{t}"
assert p==t,f"Not all stage conjunction subgoals proved: {p}/{t}"
assert not re.search(r"\[wp\]\s+\[(?:Failed|Timeout)\]|returns (?:Failed|Timeout|Unknown)|unrecognized prover answer",log),"Prover failed"
for name in ("stage_left","stage_center","stage_right"):
    assert re.search(r"(?m)^Goal Assertion '"+name+r"'",log),f"No generated goal for {name}"
assert "Alt-Ergo 2.6.4" in log and "Prover Alt-Ergo 2.5.4" not in log
result={"experiment":"B002-B4 stage conjunction splitting","status":"ISOLATED_STAGE_CONJUNCTIONS_PROVED","proved":p,"total":t,"selected":["stage_left","stage_center","stage_right"],"limits":"Selected stage goals only; complete integrated proof remains separate."}
print(json.dumps(result,indent=2))
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+"\n")
