#!/usr/bin/env python3
"""B002-B3 exact transformation: verified B2 source -> 3-lemma candidate."""
from pathlib import Path
import hashlib, re

root=Path(__file__).resolve().parents[2]
b2=root/"research/wp-import-b2/probe_b002b2.c"
b3=Path(__file__).with_name("probe_b002b3.c")
original=b2.read_text(encoding="utf-8")
actual=b3.read_text(encoding="utf-8")
a=original.index("/*@ requires imported_first_range:")
b=original.index("requires imported_second_range:",a)
statement=original[a+len("/*@ requires imported_first_range:"):b].strip()
assert statement.startswith(r"\forall double l,c,r;") and statement.endswith(";")
replacement="/*@ lemma b002b3_first_range:\n    "+statement+"\n*/\n"
expected=original[:a]+replacement+"/*@ "+original[b:]
assert actual==expected, "Candidate changes more than the one import-to-lemma substitution"
for lemma in ("b002b1_decoded_euler","b002b2_finite_euler","b002b3_first_range"):
    assert actual.count("lemma "+lemma+":")==1
imports=re.findall(r"\brequires (imported_[A-Za-z_]+):",actual)
assert imports==["imported_second_range","imported_decoded_average","imported_finite_average"],imports
assert not re.search(r"/\*@\s*axiom\s+",actual)
assert actual.count("/*@ axiomatic DriverReference")==original.count("/*@ axiomatic DriverReference")
assert r"\admit" not in actual and not re.search(r"\bsorry\b",actual)
print("B002_B3_EXACT_SOURCE_TRANSFORMATION_OK")
print("b2_sha256:",hashlib.sha256(b2.read_bytes()).hexdigest())
print("b3_sha256:",hashlib.sha256(b3.read_bytes()).hexdigest())
print("remaining_imported_premises: 3")
