#!/usr/bin/env python3
"""Research B002-B3 split-range integrity, fail-closed, source only."""
from pathlib import Path
import re, hashlib

root=Path(__file__).resolve().parents[2]
prior=root/"research/wp-import-b3/probe_b002b3.c"
candidate=Path(__file__).with_name("probe_b002b3_split.c")
old=prior.read_text(encoding="utf-8")
new=candidate.read_text(encoding="utf-8")
a=old.index("/*@ lemma b002b3_first_range:")
b=old.index("\n*/",a)
statement=old[a+len("/*@ lemma b002b3_first_range:"):b].strip()
hyp,claim=statement.split(" ==> ")
assert claim.startswith("(-4.0 <=") and claim.endswith(" <= 4.0);")
term=claim[len("(-4.0 <="):-len(" <= 4.0);")].strip()
lower=f"/*@ lemma b002b3_lower_bound:\n    {hyp} ==> (-4.0 <= {term});\n*/\n"
upper=f"/*@ lemma b002b3_upper_bound:\n    {hyp} ==> ({term} <= 4.0);\n*/\n"
assert new == old[:a]+lower+upper+old[a:], "More than two independent lemmas was changed"
for name in ("b002b1_decoded_euler","b002b2_finite_euler",
             "b002b3_lower_bound","b002b3_upper_bound","b002b3_first_range"):
    assert new.count("lemma "+name+":")==1
assert re.findall(r"\brequires (imported_[a-z_]+):",new)==[
   "imported_second_range","imported_decoded_average","imported_finite_average"]
assert not re.search(r"/\*@\s*axiom\s+",new)
assert r"\admit" not in new and not re.search(r"\bsorry\b",new)
print("EXACT_SPLIT_SOURCE_OK")
print("prior_sha256:",hashlib.sha256(prior.read_bytes()).hexdigest())
print("candidate_sha256:",hashlib.sha256(candidate.read_bytes()).hexdigest())
print("three_imports_remain")
