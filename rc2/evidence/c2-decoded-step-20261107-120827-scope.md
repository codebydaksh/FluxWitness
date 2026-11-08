# Decoded Heun step, 7 November 2026

The user-reported Lean 4.35 run in `c2-decoded-step-20261107-120827` exited 0. The reported SHA256 of `C2DecodedStep.lean` is `CC82484B56906A66A299920C72B53C663570BAC2D6FC0F6ED57B6B2BD62CE0BA`. The printed transitive axioms of `FluxWitnessC2.decoded_step_agrees` are `propext`, `Classical.choice`, and `Quot.sound`.

For 400 finite FloatLib binary64 cells with decoded magnitudes at most 2, and a real timestep of magnitude at most 9/2000, the Lean transcription of the exported Heun expression equals the benchmark's rounded step at every index. This includes both clamped neighbors, both Euler stages, the stored constants and the final rounded sum of rounded halves.

The theorem interprets rounding sites with FloatLib and takes an already decoded grid as input. The remaining interpretation obligations include relating finite WP memory reads to those decoded values and justifying the rounding correspondence on the reachable operations. Applying the result to the shipped driver's successive calls additionally requires the source and trace correspondence.

## Alternative for a real-valued trace

The exported WP C float model defines `of_f64 d = F64.t'real d`. In the saved Why3 IEEE theory, the Float64 clone maps `to_real` to `t'real`. Its `Round_to_real` axiom states that rounding the projection of a finite float fixes that real. FloatLib separately proves `Model.roundAt_toReal_eq` for its own finite values.

The original C1 theorem accepts a grid of reals. For a numerical error claim, the input grid can therefore be interpreted pointwise as the WP real projections. Under a justified common interpretation of real values and RNE rounding, Why3's fixed-point equation supplies C1's representability premise directly. This route avoids requiring a bitwise bijection of the two float types. The agreement of the two rounding functions, interpretation of the exported postcondition, and composition of successive memory states remain open. The two fixed-point facts alone do not establish that agreement.

## FloatLib rounding construction

In `c2-rounding-construction-20261107-121623`, the saved source has SHA256 `409AF5D8441D9328B12F295CF056CA63183BE906DA54FF26858E8F2762A8CF92`. The exit file records 0, the compiled object is present, and the log lists exactly `propext`, `Classical.choice`, and `Quot.sound` for both `FluxWitnessC2.binary64_floorEvenGrid` and `FluxWitnessC2.binary64_round_zero`. For nonzero inputs the first theorem identifies FloatLib rounding with the explicit floor-and-even formula at the exponent specified by the binade inequalities. The second covers zero. This closes the Lean side of that specification. The corresponding Why3 realization has been source-reviewed; a Rocq check against a pinned Flocq environment and any cross-kernel interpretation remain separate.
