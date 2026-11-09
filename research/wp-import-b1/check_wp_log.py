#!/usr/bin/env python3
"""B002-B1 proof-log gate. Fails if lemma or composition is not actually discharged."""
import json, re, sys
from pathlib import Path

p=Path(sys.argv[1])
log=p.read_text(errors="replace")
bad=[w for w in (r"\[wp\]\s+\[Timeout\]",r"Prover \S+ returns Timeout",r"\[wp\]\s+\[Failed\]",r"Error:") if re.search(w,log)]
assert not bad, f"WP errors/timeouts: {bad}"
summaries=re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)",log)
assert summaries, "No WP proof summary"
num,total=map(int,summaries[-1])
assert total>10 and num==total, f"Not all goals valid: {num}/{total}"

def check_goal(name,kind):
    # Generated goal should have a proof status in its own printed section.
    # WP prints sections separated by horizontal rules with Goal headings.
    start=re.search(
        r"(?im)^Goal\s+[^:\n]*"+re.escape(name)+r"[^:\n]*:",
        log
    )
    if start is None:
        raise AssertionError(f"Missing printed {kind} goal: {name}")
    section=log[start.start():]
    end=re.search(r"\n-{8,}\s*\n",section)
    if end: section=section[:end.start()]
    if "returns Valid" not in section:
        raise AssertionError(f"Goal not valid: {name}")
    if re.search(r"\b(?:Timeout|Unknown|Failed)\b",section):
        raise AssertionError(f"Goal contains unresolved result: {name}")

check_goal("b002b1_decoded_euler","lemma")
check_goal("decoded_update","postcondition")
check_goal("finite_update","postcondition")

result={
  "experiment":"B002-B1",
  "status":"COMPOSITION_AND_LEMMA_PROVED_IN_SAME_WP_RUN",
  "wp_goals_proved":num,"wp_goals_total":total,
  "lemma":"b002b1_decoded_euler",
  "removed_imported_caller_premise":"imported_decoded_euler",
  "remaining_imported_caller_premises":5,
  "scope":"ACSL/WP proof under remaining five imports and reference row assumptions; not C-to-Lean semantics"
}
print(json.dumps(result,indent=2))
Path("/tmp/b002b1_result.json").write_text(json.dumps(result,indent=2)+"\n")
