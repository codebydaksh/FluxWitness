# Post-RC2 supplementary results (do not alter the frozen RC2 release)

These artifacts are **after** the canonical RC2 freeze. They are included for provenance and future peer review. Do **not** describe the broader premises as frozen RC2 acceptance conditions.

## Wider initialization: conditional benchmark extension

Archived Lean 4.35 results report successful checking, with exactly the standard axiom audit of `propext`, `Classical.choice`, and `Quot.sound`, of:

| Declaration | Reported property |
|---|---|
| `FluxWitness400.model_benchmark_wide` | Allows initial per-cell error ≤ `10⁻¹⁵`; keeps final model error ≤ `7.05 × 10⁻⁹` over 400 cells and 223 steps |
| `FluxWitnessC3.driver223_of_wp_wide` | Transfers the bound to 223 driver calls under the explicit allocation, layout, call and WP-interpretation hypotheses |
| `FluxWitnessC4.reference223_wide` | Constructs finite in-range binary64 representatives and the interpreted successor updates through step 223 |

The original RC2 bound is `2.4854 × 10⁻¹⁶`. The wider result is a distinct candidate, not an RC2 rewrite. See `supplements/wider-initialization/README.md` and archived proofs.

## Four historical local builds

Local WSL tests of `glibc -O0`, `glibc -O2`, `musl -O0`, and `musl -O2` all certified the original RC2 initialization premise. Compiler optimization pairs for each math library produced bit-identical exported 400-cell input arrays. Five cells differed by +1 binary64 ulp under musl versus glibc (zero-based: 66, 68, 122, 305, 317); the worst cell was 238 for all builds. Maximum certified upper bound was approximately `2.485378074949 × 10⁻¹⁶`, leaving approximately `2.192505078 × 10⁻²¹` headroom versus frozen RC2. These are observations for four builds on one host, **not** deductive verification of an uninstrumented binary or portability across platforms. The raw cell arrays, hashes and certificates are in `supplements/wider-initialization/builds/`.

## Nominal cosine reference

The nominal theorem reports the same `7.05 × 10⁻⁹` final conditional bound against analytic diffusivity `1/100` at time `1` on `[-3,3]`, with initial error ≤ `10⁻¹⁵`. The analytically quantified difference between effective and nominal references is ≤ `5 × 10⁻²⁰` per cell. This is **not** the frozen effective-diffusivity reference; see `supplements/nominal-reference/README.md` and result logs. The historical local run used cached dependencies. The independent clean-source rebuild recipe is untested.

## Remaining gaps

- Clean-machine installation and rebuild from a blank dependency cache; pin external revisions and retain logs.
- End-to-end verified interpretation of WP states and the uninstrumented C program's initialization, allocations, math library behavior and compilation.
- Cross-platform evidence beyond the four WSL local build variants.
- Version-specific DOI/deposit is not supplied; link to one only after independently publishing it.
