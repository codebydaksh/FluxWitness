# FluxWitness: conditional verification of a C heat solver

**Frozen RC2 original:** 2026-11-08. The unchanged original archive is preserved separately with SHA-256 `d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0`. The published RC2 distribution is path-redacted and has a **different** SHA-256. See [provenance](docs/DISTRIBUTION_PROVENANCE.md).

The **rounded Lean model** proves a **pointwise final error ≤ 7.05 × 10⁻⁹** against the specified effective-diffusivity cosine reference after 223 stored-timestep Heun steps on 400 cells, **conditional on initial per-cell error ≤ 2.4854 × 10⁻¹⁶**. The final reference is evaluated at 223 times the stored timestep. This is **not** an unconditional theorem about arbitrary compiled C executables, compilers or math libraries.

## Evidence at a glance

- The RC2 Lean model, construction, conditional driver, and reference proof files are under [`rc2/lean/`](rc2/lean/). The audit module [`ReleaseAudit.lean`](rc2/lean/ReleaseAudit.lean) prints the axioms of six declarations. The archived runner reports Lean 4.35 exit 0 and exactly `propext`, `Classical.choice`, and `Quot.sound`; these historical runs have **not** been independently reproduced in a clean environment for this publication kit.
- Frama-C/WP evidence for the shipped step body and an extracted C driver is in [`rc2/evidence/`](rc2/evidence/). The relevant contracts, abstractions, floating-point interpretations, initialization, layout, and compilation/runtime assumptions remain explicit trust boundaries.
- One instrumented C invocation exported 400 initial values. Its exact-rational checker certified the RC2 initial-error premise. The observed peak final difference from the numerically evaluated cosine reference was about **7.027 × 10⁻⁹**; it is an empirical result, not the proof itself.
- A separate arithmetic-comparison harness recorded peak C versus exact-real Heun discrepancy **1.7243 × 10⁻¹⁵** after 223 steps, versus the model's accumulated rounding budget **6.0433 × 10⁻¹³**. This is a different comparison from the model-to-PDE theorem.

## Figures

![Final heat profile and change from initialization](figures/heat-profile.png)

![Per-cell final error versus effective-diffusivity cosine reference](figures/heat-error.png)

![C versus exact-real Heun arithmetic discrepancy](figures/heat-rounding-error.png)

The first two figures and generator script are preserved under [`publication-source/`](publication-source/), and the third figure's underlying CSV, C harness, script and recorded log are under [`supplements/rounding/`](supplements/rounding/). Original PDFs are also in `figures/`.

## How the repository is organized

| Directory | Meaning |
|---|---|
| [`rc2/`](rc2/) | Source and path-redacted evidence derived from the frozen RC2 archive: Lean, C, evidence, trust ledger, manifests, replay instructions |
| [`publication-source/`](publication-source/) | Figure source and generator, without the nested original archive |
| [`supplements/rounding/`](supplements/rounding/) | Rounding-comparison figure, code, data and logs; accompanies RC2 |
| [`supplements/wider-initialization/`](supplements/wider-initialization/) | **Post-RC2** wider-premise Lean theorems and four-build C initialization certificates |
| [`supplements/nominal-reference/`](supplements/nominal-reference/) | **Post-RC2** nominal-diffusivity, time-1 reference theorem and evidence |
| [`release-assets/`](release-assets/) | Five public-distribution ZIPs with separate checksums |
| [`docs/`](docs/) | Frozen and follow-up notes, SHA-256 manifest, publication instructions |

**Post-RC2 (not part of frozen release):** Separate candidate declarations permit initial pointwise error as large as `10⁻¹⁵` while preserving the `7.05 × 10⁻⁹` model bound; wider conditional driver/reference results are recorded. A separate nominal-reference result covers diffusivity `1/100` and time `1`. The four local glibc/musl builds all satisfied even the original RC2 initial error bound. See [`docs/POST_RC2_RESULTS.md`](docs/POST_RC2_RESULTS.md) for limitations.

## Reproduce or independently audit

Read [`rc2/README.md`](rc2/README.md) first. In an environment with Lean 4.35, Lake and pinned dependencies, the suggested clean-source check is to run **`lake build ReleaseAudit` from `rc2/lean/`**. A fresh clean-dependency build has not yet been demonstrated; no proof commands were rerun to prepare this repository. Archived successful runs used pinned local dependency objects. RC2 provides a Windows replay script as well as Frama-C/WP and Rocq procedures. Post-RC2 supplementary source-rebuild recipes are separate and not independently tested.

Before redistributing historical logs publicly, review them for local filesystem paths. The standalone replay log was later supplied. A **path-redacted copy** and its provenance/checksum note are in [`docs/replay-public.log`](docs/replay-public.log) and [`docs/REPLAY_LOG_NOTE.md`](docs/REPLAY_LOG_NOTE.md). The original unredacted log is not included in this public-facing kit. A formal license and DOI have **not** been supplied and are not inferred.

To verify the five published ZIPs, after importing the complete distribution: `sha256sum -c docs/RELEASE_ASSET_SHA256SUMS.txt` (Linux/WSL). GitHub RC2 release notes are in [`docs/RC2_RELEASE_NOTES.template.md`](docs/RC2_RELEASE_NOTES.template.md).
**Distribution status:** The source tree, figures and release ZIPs have been prepared for import. The release workflow should not run until these assets are committed and their checksums pass. The published source ZIP and its recorded original must not be represented as byte-identical.
