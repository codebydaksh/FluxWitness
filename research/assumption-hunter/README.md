# Assumption Hunter B001: conditional WP expression bridge

**Research-only, not part of frozen RC2. No C-to-Lean correspondence has been discharged yet.**

Source anchors:
- `rc2/lean/C2DecodedStep.lean`: `FluxWitnessC2.interpretedStep`
- `rc2/lean/C3DriverLoop.lean`: `FluxWitnessC3.driver223_of_wp`
- `rc2/evidence/wp-reference-interpretation-08zrp8uz/probe.c`: source ACSL formulae `c5_e`, `c5_update`
- `rc2/evidence/wp-reference-interpretation-08zrp8uz/result.json`: archived WP status, including imported assumptions

Proposed Lean declarations:
1. `AssumptionHunterBridge.wpUpdate_eq_interpretedStep`: equality **between two Lean expressions** (manual transcription of ACSL vs existing C2 definition). No WP or C semantics are verified by this declaration.
2. `AssumptionHunterBridge.driver223_of_explicit_wp`: specializes original C3 theorem to an explicit update; still assumes `wp_call_explicit`, which is an unverified C/WP-to-Lean transfer premise.

**Open:** establish that the exported Frama-C/WP C postcondition has exactly the semantics of `wpUpdate`; imported WP scalar/range premises; actual state/memory layout and step correspondence; compiler and runtime behaviors, and initialization transfer.

Run `bash research/assumption-hunter/run_lean.sh` after installing pinned Lean/FloatLib dependencies. Inspect the actual axiom audit, not just a workflow green check. No claimed proof until the actual Lean build log is examined.

Stop gate: If Lean rejects the file, treat it as unverified work in progress. If Lean accepts it, that only establishes an intra-Lean equality and conditional corollary, **not** end-to-end binary verification.
