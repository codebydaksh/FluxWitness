#!/usr/bin/env python3
"""Pinned-source checker only; this is NOT an ACSL semantics checker."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[2]
src = root / "rc2/evidence/wp-reference-interpretation-08zrp8uz/probe.c"
lean = Path(__file__).with_name("WPInterpretationBridge.lean")
expected = "231047633ea7001e4c48fce8321bd72ca8f2bf17d9909247da36b56c140d70bc"
assert src.is_file() and lean.is_file()
actual = hashlib.sha256(src.read_bytes()).hexdigest()
assert actual == expected, f"source SHA changed: {actual}"
wp = src.read_text()
proof = lean.read_text()
for term in ("logic real c5_e(", "logic real c5_update(", "logic integer c5_l(", "logic integer c5_r(", "5764607523034235.0 / 576460752303423488.0", "4150517416584649.0 / 18446744073709551616.0"):
    assert term in wp, f"missing WP source term: {term}"
for term in ("theorem wpUpdate_eq_interpretedStep", "theorem driver223_of_explicit_wp", "#print axioms AssumptionHunterBridge.driver223_of_explicit_wp"):
    assert term in proof, f"missing Lean term: {term}"
assert not re.search(r"(?m)^\s*(sorry|admit|axiom)\b", proof)
print(json.dumps({"source_sha256":actual,"lean_sha256":hashlib.sha256(lean.read_bytes()).hexdigest(),"result":"PINNED_SOURCE_CHECK_PASSED", "limits":"No statement about semantic equivalence of ACSL and Lean"}))
