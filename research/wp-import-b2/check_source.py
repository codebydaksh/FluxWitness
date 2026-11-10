#!/usr/bin/env python3
"""B002-B2 exact-transformation integrity check, not a formal proof."""
from pathlib import Path
import hashlib
import re

root = Path(__file__).resolve().parents[2]
b1 = root / "research/wp-import-b1/probe_b002b1.c"
b2 = Path(__file__).with_name("probe_b002b2.c")
original = b1.read_text(encoding="utf-8")
actual = b2.read_text(encoding="utf-8")
start = original.index("/*@ requires imported_finite_euler:")
end = original.index("requires imported_first_range:", start)
stmt = original[start + len("/*@ requires imported_finite_euler:"):end].strip()
assert stmt.startswith(r"\forall double l,c,r;") and stmt.endswith(";")
lemma = "/*@ lemma b002b2_finite_euler:\n    " + stmt + "\n*/\n"
expected = original[:start] + lemma + "/*@ " + original[end:]
assert actual == expected, "Unexpected changes relative to verified B002-B1 candidate"
assert actual.count("lemma b002b1_decoded_euler:") == 1
assert actual.count("lemma b002b2_finite_euler:") == 1
assert "requires imported_decoded_euler:" not in actual
assert "requires imported_finite_euler:" not in actual
imports = re.findall(r"\brequires (imported_[A-Za-z_]+):", actual)
assert imports == [
    "imported_first_range",
    "imported_second_range",
    "imported_decoded_average",
    "imported_finite_average",
], imports
# Preserve all original axiomatic declarations; do not add axioms or admissions.
assert not re.search(r"/\*@\s*axiom\s+", actual)
assert actual.count("/*@ axiomatic DriverReference") == original.count("/*@ axiomatic DriverReference")
assert r"\admit" not in actual and not re.search(r"\bsorry\b", actual)
print("B002_B2_EXACT_SOURCE_TRANSFORMATION_OK")
print("b1_sha256:", hashlib.sha256(b1.read_bytes()).hexdigest())
print("b2_sha256:", hashlib.sha256(b2.read_bytes()).hexdigest())
print("remaining_imported_caller_premises: 4")
