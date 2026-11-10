#!/usr/bin/env python3
"""Fail-closed exact-diff audit for B002-B4 stencil-cut diagnostic."""
from pathlib import Path
import re, hashlib
root=Path(__file__).resolve().parents[2]
old=root/"research/wp-import-b4/probe_b002b4.c"
new=Path(__file__).with_name("probe_b002b4_cut.c")
a=old.read_text()
b=new.read_text()
start=b.index("/*@ lemma b002b4_stencil_range:")
end=b.index("*/",start)+2
added=b[start:end]+"\n"
assert b == a.replace("/*@ lemma b002b4_second_lower:",added+"/*@ lemma b002b4_second_lower:",1)
assert b.count("lemma b002b4_stencil_range:")==1
assert "requires imported_second_range:" not in b
assert re.findall(r"\brequires (imported_[a-z_]+):",b)==["imported_decoded_average","imported_finite_average"]
assert not re.search(r"/\*@\s*axiom\s+|\bsorry\b|\\admit",b)
print("EXACT_STENCIL_CUT_SOURCE_OK")
print("parent_sha256:",hashlib.sha256(old.read_bytes()).hexdigest())
print("candidate_sha256:",hashlib.sha256(new.read_bytes()).hexdigest())
