#!/usr/bin/env python3
"""Fail-closed B002-B1 source transposition check; not a theorem checker."""
from pathlib import Path
import hashlib

root=Path(__file__).resolve().parents[2]
prior=root/"rc2/evidence/wp-reference-interpretation-08zrp8uz/probe.c"
candidate=Path(__file__).with_name("probe_b002b1.c")
src=prior.read_bytes()
expected_sha="231047633ea7001e4c48fce8321bd72ca8f2bf17d9909247da36b56c140d70bc"
assert hashlib.sha256(src).hexdigest()==expected_sha, "Original WP source is not the pinned version"
original=src.decode("utf-8")
a=original.index("/*@ requires imported_decoded_euler:")
b=original.index("requires imported_finite_euler:",a)
stmt=original[a+len("/*@ requires imported_decoded_euler:"):b].strip()
assert stmt.startswith(r"\forall double l,c,r;") and stmt.endswith(";")
lemma="/*@ lemma b002b1_decoded_euler:\n    "+stmt+"\n*/\n"
generated=original[:a]+lemma+"/*@ "+original[b:]
actual=candidate.read_text(encoding="utf-8")
assert actual==generated, "Candidate differs from one-clause replacement"
assert "requires imported_decoded_euler:" not in actual
assert actual.count("lemma b002b1_decoded_euler:")==1
for name in ["imported_finite_euler","imported_first_range","imported_second_range",
             "imported_decoded_average","imported_finite_average"]:
    assert generated.count("requires "+name+":")==1, name
assert actual.count("/*@ axiomatic DriverReference") == original.count("/*@ axiomatic DriverReference")
assert not __import__("re").search(r"/\*@\s*axiom\s+", actual)
assert r"\admit" not in actual
print("SOURCE_REPLACEMENT_OK")
print("original_sha256:",hashlib.sha256(src).hexdigest())
print("candidate_sha256:",hashlib.sha256(candidate.read_bytes()).hexdigest())
print("remaining_imports: 5")
print("note: static check does not verify ACSL or WP semantics")
