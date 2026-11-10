#!/usr/bin/env python3
"""Fail closed: require 17/17 and independent WP results for three lemmas."""
from pathlib import Path
import json, re, sys

log=Path(sys.argv[1]).read_text(encoding="utf-8",errors="replace")
failures=[
    r"\[wp\]\s+\[Timeout\]",
    r"returns (?:Timeout|Unknown|Failed)",
    r"\[wp\]\s+\[Failed\]",
    r"(?im)^.*\berror:"
]
assert all(not re.search(expr,log) for expr in failures), "WP timeout, failure or error detected"
summaries=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",log)
assert len(summaries)==1, f"Unexpected WP summary: {summaries!r}"
proved,total=map(int,summaries[0])
assert (proved,total)==(17,17), f"Expected 17/17; got {proved}/{total}"
assert "Alt-Ergo 2.6.4" in log and "Prover Alt-Ergo 2.5.4" not in log
for name in ("imported_decoded_euler","imported_finite_euler","imported_first_range"):
    assert f"Pre-condition '{name}'" not in log, f"Removed property still treated as caller assumption: {name}"
for name in ("imported_second_range","imported_decoded_average","imported_finite_average"):
    assert f"Pre-condition '{name}'" in log, f"Expected retained assumption not visible: {name}"

def ensure_valid(title):
    target=re.search(r"(?m)^Goal "+re.escape(title)+r"[^\n]*:\s*$",log)
    assert target, f"Missing expected proof goal: {title}"
    tail=log[target.end():]
    boundary=re.search(r"\n-{8,}\s*\n",tail)
    assert boundary, f"No proof-goal boundary: {title}"
    section=tail[:boundary.start()]
    assert re.search(r"Prover Alt-Ergo 2\.6\.4 returns Valid|Prover Qed returns Valid",section), f"Goal not Valid: {title}"
    assert not re.search(r"returns (?:Timeout|Unknown|Failed)",section), title

for goal in [
    "Lemma 'b002b1_decoded_euler'",
    "Lemma 'b002b2_finite_euler'",
    "Lemma 'b002b3_first_range'",
    "Post-condition 'decoded_update' in 'compare_update'",
    "Post-condition 'finite_update' in 'compare_update'",
]:
    ensure_valid(goal)

result={
    "experiment":"B002-B3",
    "status":"THREE_GLOBAL_WP_LEMMAS_AND_COMPOSITION_PROVED_IN_SAME_RUN",
    "proved":proved,"total":total,
    "proved_lemmas":["b002b1_decoded_euler","b002b2_finite_euler","b002b3_first_range"],
    "remaining_imports":["imported_second_range","imported_decoded_average","imported_finite_average"],
    "limitations":"Conditional ACSL/WP model result. Cross-tool, runtime and memory correspondence remain open."
}
print(json.dumps(result,indent=2))
if len(sys.argv)>2:
    Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
