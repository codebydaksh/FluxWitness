#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
python3 "$HERE/verify_source.py"
cd "$ROOT/rc2/lean"
lake lean "$HERE/WPInterpretationBridge.lean" 2>&1 | tee "$HERE/lean-build.log"
! grep -E "error:|sorryAx" "$HERE/lean-build.log"
grep -F 'AssumptionHunterBridge.wpUpdate_eq_interpretedStep' "$HERE/lean-build.log"
grep -F 'AssumptionHunterBridge.driver223_of_explicit_wp' "$HERE/lean-build.log"
