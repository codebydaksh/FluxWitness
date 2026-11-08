# FluxWitness Heat RC2 | public distribution

**Frozen theorem statement (2026-11-08).** For 400 cells and 223 stored-timestep Heun updates, the rounded Lean model has a pointwise final error at most **7.05 × 10⁻⁹** against the specified effective-diffusivity cosine reference, conditional on initial pointwise error at most **2.4854 × 10⁻¹⁶**.

An exact-rational checker certified the premise for 400 initial values in one instrumented C run, which exhibited about **7.027 × 10⁻⁹** peak final difference. A separate arithmetic comparison gave **1.7243 × 10⁻¹⁵** C versus exact-real Heun discrepancy against a **6.0433 × 10⁻¹³** model budget. These observations are not universal compiled-binary guarantees.

Frama-C/WP checked the shipped step and an extracted driver under explicit contracts. The cross-tool interpretation, initialization, allocation, libm and compilation/runtime remain trust conditions.

**Integrity:** The unchanged original RC2 ZIP is retained separately with SHA-256 `d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0`. The release ZIP distributed here is a path-redacted derivative, with a **different** checksum; see [provenance](https://github.com/__REPOSITORY__/blob/__TAG__/docs/DISTRIBUTION_PROVENANCE.md).

![Heat profile](https://raw.githubusercontent.com/__REPOSITORY__/__TAG__/figures/heat-profile.png)

![Final error](https://raw.githubusercontent.com/__REPOSITORY__/__TAG__/figures/heat-error.png)

![Arithmetic discrepancy](https://raw.githubusercontent.com/__REPOSITORY__/__TAG__/figures/heat-rounding-error.png)

The wider-initialization and nominal-reference supplements are post-RC2 results, not modifications of the frozen theorem.
