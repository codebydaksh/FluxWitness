# FluxWitness Heat RC2 | conditional verification of the 1D cosine heat benchmark

**Frozen RC2 (2026-11-08).** For a 400-cell, 223-step Heun evolution, Lean proves that the **rounded model** has per-cell error at most **7.05 × 10⁻⁹**, measured against the specified effective-diffusivity cosine reference at the stored elapsed time, **provided the initial per-cell error is at most 2.4854 × 10⁻¹⁶**.

A rational checker certified the initial premise for 400 values from one instrumented C invocation. That run's final output differed from the numerically evaluated reference by at most approximately **7.027 × 10⁻⁹**. Separately, a C-versus-exact-real Heun harness recorded maximum arithmetic discrepancy **1.7243 × 10⁻¹⁵** at step 223, compared with an accumulated model rounding budget **6.0433 × 10⁻¹³**. These measurements do not establish universal properties of compiled binaries.

Frama-C/WP checked the shipped step body and an extracted driver under explicit contracts. Lean and Rocq checked the rounding formula. The cross-tool interpretation, initialization, allocation/layout, library contracts and compilation remain trust conditions. No unconditional end-to-end C binary verification is claimed.

**Public-distribution asset:** `FluxWitness-Heat-Conditional-20261108-rc2-public.zip`  
**Original frozen RC2 SHA-256 (not the public archive hash):** `d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0`

**Release attachments**

1. `FluxWitness-Heat-Conditional-20261108-rc2-public.zip`: Lean/C sources, audit, evidence, trust ledger and replay instructions.
2. `FluxWitness-Heat-Publication-public.zip`: heat-profile and final-error figures, PDFs, generator script, without the nested original archive.
3. `heat-rounding-figure-supplement-20261108.zip`: rounding-error figure, CSV, harness, oracle script and archived log.

![Final heat profile](../../blob/__TAG__/figures/heat-profile.png?raw=true)

![Per-cell final absolute error and proved bound](../../blob/__TAG__/figures/heat-error.png?raw=true)

![C versus exact-real Heun rounding discrepancy](../../blob/__TAG__/figures/heat-rounding-error.png?raw=true)

**Scope:** The frozen RC2 initial premise is `2.4854 × 10⁻¹⁶`, **not** the later `10⁻¹⁵` wider-premise theorem. Post-RC2 supplements are maintained separately in this repository and are not part of this release. Independent clean-dependency reproduction remains open. A path-redacted copy of the subsequently provided Lean replay log is tracked at [`docs/replay-public.log`](https://github.com/__REPOSITORY__/blob/__TAG__/docs/replay-public.log). This historical log is not a substitute for independent clean-dependency reproduction.

**Distribution note:** These named public archives contain only path-redacted copies of selected historical logs. See [`docs/DISTRIBUTION_PROVENANCE.md`](https://github.com/__REPOSITORY__/blob/__TAG__/docs/DISTRIBUTION_PROVENANCE.md). The untouched original archive is retained separately; this public asset has a distinct checksum.
