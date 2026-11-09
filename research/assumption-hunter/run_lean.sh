#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
python3 "$HERE/verify_source.py"
cd "$ROOT/rc2/lean"
# pipefail preserves the Lean exit status. Audit only the actual compiler output.
lake lean "$HERE/WPInterpretationBridge.lean" 2>&1 | tee "$HERE/lean-build.log"
python3 - "$HERE/lean-build.log" <<'PY'
import re, sys
from pathlib import Path
log = Path(sys.argv[1]).read_text()
names = [
    "AssumptionHunterBridge.wpUpdate_eq_interpretedStep",
    "AssumptionHunterBridge.driver223_of_explicit_wp",
]
expected = {"propext", "Classical.choice", "Quot.sound"}
if re.search(r"(?m)^.*(?:error:|sorryAx)", log):
    raise SystemExit("Compilation warning/error or sorryAx found")
for name in names:
    pattern = re.escape("'" + name + "' depends on axioms:") + r"\s*\[([^\]]+)\]"
    hits = re.findall(pattern, log)
    if len(hits) != 1:
        raise SystemExit(f"Axiom audit missing or ambiguous: {name}")
    found = {x.strip() for x in hits[0].split(",")}
    if found != expected:
        raise SystemExit(f"Unexpected axiom list for {name}: {sorted(found)}")
    print("AXIOM_AUDIT_ACCEPTED:", name, sorted(found))
print("B001_LEAN_CHECK_ACCEPTED_CONDITIONALLY")
PY
