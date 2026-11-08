# FluxWitness nominal heat benchmark

Post-RC2 supplement. FluxWitness400.nominal_benchmark bounds the pointwise final error of the rounded Lean evolution by 7.05e-9 on 400 cells after 223 stored-timestep Heun steps, given initial cosine error at most 1e-15. The analytic comparison uses diffusivity 1/100 and time 1 on [-3,3]. The stored schedule and arithmetic are unchanged. The effective and nominal references differ by at most 5e-20 per cell. The existing conditional C-driver result cites the effective reference. Executable transfer retains the RC2 trust conditions.

Baseline ZIP SHA-256: d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0
Wider initialization ZIP SHA-256: 347c25d9105f61806c0371279363f4a6b1afdbce1bf790c628dce3fdaa15cdbd

The lean directory contains the four additional source modules needed on top of RC2. For a source rebuild, extract RC2 to a fresh directory, copy these modules into its lean directory, and append the following to that copy's lean/lakefile.lean:

    lean_lib WiderInitial
    lean_lib NominalHeatParameters
    lean_lib NominalHeatProfile
    lean_lib NominalHeatBenchmark

From that lean directory run lake build NominalHeatBenchmark. This portable recipe has not been independently tested. Accepted local runs used cached dependencies. Each evidence directory contains the original stdout, stderr and result record. Compiled objects were checked against the recorded hashes during packaging and are omitted from the supplement.
