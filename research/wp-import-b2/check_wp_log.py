#!/usr/bin/env python3
"""Strict verification gate for B002-B2: 16/16, both lemmas, both postconditions."""
from pathlib import Path
import re
import sys
import json

log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
bad = [x for x in [r"\[wp\]\s+\[Timeout\]", r"returns Timeout",
                    r"returns Unknown", r"returns Failed", r"\[wp\]\s+\[Failed\]",
                    r"(?m)^.*\berror:"] if re.search(x, log, flags=re.I)]
assert not bad, "Unresolved WP goals or errors: " + repr(bad)
summaries = re.findall(r"\[wp\]\s+Proved goals:\s*(\d+)\s*/\s*(\d+)", log)
assert len(summaries) == 1, f"Unexpected proof summary count: {summaries}"
proved, total = map(int, summaries[0])
assert (proved, total) == (16, 16), f"Expected 16/16, got {proved}/{total}"
assert "Alt-Ergo 2.6.4" in log, "Missing proven pinned prover version"
assert "Prover Alt-Ergo 2.5.4" not in log
assert "Pre-condition 'imported_decoded_euler'" not in log
assert "Pre-condition 'imported_finite_euler'" not in log

def goal_valid(title):
    prefix = re.search(r"(?m)^Goal " + re.escape(title) + r"[^\n]*:\s*$", log)
    assert prefix, f"Goal missing: {title}"
    section = log[prefix.end():]
    cutoff = re.search(r"\n-{8,}\s*\n", section)
    assert cutoff, f"Goal section not terminated: {title}"
    section = section[:cutoff.start()]
    assert re.search(r"Prover Alt-Ergo 2\.6\.4 returns Valid|Prover Qed returns Valid", section), f"Goal not Valid: {title}"
    assert not re.search(r"returns (?:Timeout|Unknown|Failed)", section), title

for label in [
    "Lemma 'b002b1_decoded_euler'",
    "Lemma 'b002b2_finite_euler'",
    "Post-condition 'decoded_update' in 'compare_update'",
    "Post-condition 'finite_update' in 'compare_update'",
]:
    goal_valid(label)

result = {
    "experiment": "B002-B2",
    "status": "TWO_LEMMAS_AND_COMPOSITION_PROVED_IN_SAME_WP_RUN",
    "wp_goals_proved": proved,
    "wp_goals_total": total,
    "checked_lemmas": ["b002b1_decoded_euler", "b002b2_finite_euler"],
    "removed_imports": ["imported_decoded_euler", "imported_finite_euler"],
    "remaining_imports": [
        "imported_first_range", "imported_second_range",
        "imported_decoded_average", "imported_finite_average"],
    "scope": "WP functional proof conditional on four imports, reference-row inputs and WP/Why3 semantics; no C/Lean equivalence"
}
print(json.dumps(result, indent=2))
if len(sys.argv) > 2:
    Path(sys.argv[2]).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
