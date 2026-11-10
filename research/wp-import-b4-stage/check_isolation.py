#!/usr/bin/env python3
"""Fail closed on missing/invalid isolated-stage VCs. Do not claim 23/23."""
from pathlib import Path
import json, re, sys

root=Path(sys.argv[1])
status={}
for stage in ("baseline","stage_left","stage_center","stage_right"):
    f=root/(stage+".log")
    assert f.is_file(),f"Missing log: {f}"
    s=f.read_text(errors="replace")
    exitcode=(root/(stage+".exit")).read_text().strip()
    goals=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",s)
    outcome={"exit":exitcode,"summaries":goals}
    if stage!="baseline":
        expected="Goal Assertion '"+stage+"'"
        outcome["goal_present"]=expected in s
        m=re.search(r"(?m)^Goal Assertion '"+re.escape(stage)+r"'\b?[^\n]*:",s)
        # The \b after closing quote may not match; fall back to exact prefix.
        if m is None:
            m=re.search(r"(?m)^Goal Assertion '"+re.escape(stage)+r"'[^\n]*:",s)
        if m:
            sec=s[m.end():]
            boundary=re.search(r"\n-{8,}\s*\n",sec)
            if boundary: sec=sec[:boundary.start()]
            outcome["goal_valid"]=bool(re.search(r"Prover (?:Alt-Ergo 2\.6\.4|Qed) returns Valid",sec))
            outcome["goal_failed"]=bool(re.search(r"returns (?:Failed|Timeout|Unknown)|unrecognized prover answer",sec))
        else:
            outcome["goal_valid"]=False
            outcome["goal_failed"]=False
    outcome["output_has_error"]=bool(re.search(r"(?im)^.*(?:unknown option|option .* not found|syntax error|error:)",s))
    outcome["failed_prover_answers"]=len(re.findall(r"returns Failed|unrecognized prover answer",s))
    outcome["timed_out_prover_answers"]=len(re.findall(r"returns Timeout|\[wp\]\s+\[Timeout\]",s))
    status[stage]=outcome

(root/"isolation-results.json").write_text(json.dumps(status,indent=2)+"\n")
print(json.dumps(status,indent=2))
# A selector error, missing selected VC, or failed goal is a genuine failure.
# The baseline is a diagnostic only; do not reject because its old second-range
# lemmas are still unproved. All isolated selected assertions must be valid.
for stage in ("stage_left","stage_center","stage_right"):
    item=status[stage]
    assert item["exit"]=="0",f"{stage}: Frama-C did not return success"
    assert item["goal_present"] and item["goal_valid"] and not item["goal_failed"],f"{stage}: not Valid"
    assert not item["output_has_error"],f"{stage}: command/prover error"
    assert item["summaries"] and all(int(p)==int(t) for p,t in item["summaries"]),f"{stage}: other selected goals unproved"
assert status["baseline"]["summaries"],"Baseline output missing summary"
print("THREE_INDEPENDENT_STAGE_GOALS_VALID_DIAGNOSTIC_ONLY")
