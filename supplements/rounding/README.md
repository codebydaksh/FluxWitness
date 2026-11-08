# Rounding error in the 400-cell cosine heat benchmark

Across six sampled steps, the figure compares the maximum absolute difference across cells between the C harness state and exact-real Heun evolution from the same initial doubles, with stored D, dx-squared and dt. At step 223 the recorded discrepancy is 1.724327579819043e-15. The accumulated model rounding budget is 223 times 271/10^17, or 6.0433e-13.

The harness includes the shipped kernel and supplies its own initialization and driver. It exports binary64 cells with %a. Python imports the cells exactly into Fraction and compares the error to the rational threshold before converting the maximum to a floating-point value for display and CSV. Lines between observed steps are visual guides. This measures arithmetic discrepancy for the historical harness run. The 7.05e-9 model-to-PDE bound concerns a different comparison.

The supplied PNG, CSV, log, harness and oracle are archived originals matched to the artifact manifest. The kernel source matches the RC2 source hash. Packaging did not rerun the experiment. This supplement accompanies frozen RC2, SHA256 d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0.

## Optional regeneration on Linux

From this supplement's root in a fresh copy, run the commands below. The compiler and runtime can affect the observed data. Python's standard library computes the CSV; matplotlib is needed to render the PNG.

    mkdir replay
    gcc -std=c11 -O0 -ffp-contract=off -DIC_COSINE -Ic_code evidence/differential/harness_dump.c -lm -o replay/harness
    python3 evidence/differential/plot_from_c.py ./replay/harness c_code/heat_1d_v2.c replay

Use the six within-bound verdicts in the oracle output when inspecting a new run.
