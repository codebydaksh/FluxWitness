#!/usr/bin/env python3
"""Exact B002-B4 source transposition against accepted B002-B3 split source."""
from pathlib import Path
import re,hashlib
root=Path(__file__).resolve().parents[2]
oldp=root/"research/wp-import-b3-split/probe_b002b3_split.c"
newp=Path(__file__).with_name("probe_b002b4.c")
old=oldp.read_text()
new=newp.read_text()
a=old.index("/*@ requires imported_second_range:")
b=old.index("requires imported_decoded_average:",a)
statement=old[a+len("/*@ requires imported_second_range:"):b].strip()
hyp,claim=statement.split(" ==> ")
assert claim.startswith("(-12.0 <=") and claim.endswith(" <= 12.0);")
term=claim[len("(-12.0 <="):-len(" <= 12.0);")].strip()
low=f"/*@ lemma b002b4_second_lower:\n    {hyp} ==> (-12.0 <= {term});\n*/\n"
high=f"/*@ lemma b002b4_second_upper:\n    {hyp} ==> ({term} <= 12.0);\n*/\n"
whole=f"/*@ lemma b002b4_second_range:\n    {statement}\n*/\n"
assert new==old[:a]+low+high+whole+"/*@ "+old[b:],"Source mismatch (beyond one import replacement)"
assert re.findall(r"\brequires (imported_[a-z_]+):",new)==["imported_decoded_average","imported_finite_average"]
for name in ["b002b1_decoded_euler","b002b2_finite_euler","b002b3_lower_bound",
             "b002b3_upper_bound","b002b3_first_range","b002b4_second_lower",
             "b002b4_second_upper","b002b4_second_range"]:
    assert new.count("lemma "+name+":")==1,name
assert not re.search(r"/\*@\s*axiom\s+|\bsorry\b|\\admit",new)
print("B002_B4_SOURCE_MATCH_OK")
print("previous_sha256:",hashlib.sha256(oldp.read_bytes()).hexdigest())
print("candidate_sha256:",hashlib.sha256(newp.read_bytes()).hexdigest())
print("remaining_imports: 2")
