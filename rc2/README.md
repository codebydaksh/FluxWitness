# FluxWitness · conditional verification of the 1D cosine heat benchmark

For 400 cells and 223 Heun steps, the rounded Lean evolution has pointwise final error at most **7.05 × 10⁻⁹** against the specified effective-diffusivity cosine reference, given initial pointwise error at most **2.4854 × 10⁻¹⁶**. The theorem evaluates the reference at 223 times the stored timestep. The public claim concerns this benchmark and its clamped boundaries.

| Layer | Evidence and scope |
|---|---|
| Numerical analysis | The finite-grid stability, consistency and accumulated error proofs specialize to this 400-cell problem. |
| Binary64 model | Lean 4.35 combines rounding, halving, the stored coefficient and the benchmark. C4 constructs finite representatives through step 223. The audited Lean declarations use propext, Classical.choice and Quot.sound. |
| C source and execution | Frama-C WP checks the shipped step body and an extraction of the shipped driver loop under explicit contracts. Rocq and Lean each check the nearest-even formula. Their mathematical identification and the lifting of separately proved scalar WP contracts are reviewed across tools. |

**Trust and scope.** Transfer to a successful C execution depends on the allocation model and buffer layout, separation, initialization, the restricted libm ceiling contract, and the interpretation of WP states and float operations. The rational initial-error certificate covers one instrumented cosine invocation. Transfer to an uninstrumented GCC binary additionally depends on initialization correspondence and the compiler/runtime. A universal binary-execution theorem remains open. The Gaussian build, other equations, and research novelty are outside the release claim. See the [chronological premise and range ledger](evidence/trace-premise-review-20261107.md); later dated results supersede earlier open statuses.

## Reproduction

The individual logs are archived evidence. A fresh replay of the packaged Lean sources is the release-candidate acceptance check.

1. On the original Windows machine, run `python replay.py PATH_TO_PINNED_FLOATLIB_WORKSPACE PATH_TO_PINNED_LEAN_EXE` from the extracted bundle. This verifies the manifest and builds all local modules in import order in a new directory using the existing dependency objects. It checks the six final axiom lists. The run uses a single worker, a 2 GiB Lean memory setting and a 25-minute total timeout. This replay trusts the prebuilt third-party dependencies.
2. Independently, from `lean/` with Lake and the toolchain in `lean-toolchain`, use `lake build ReleaseAudit` with the packaged manifest. This is the portable clean-dependency build route; it requires access to the pinned upstream repositories. A successful run from this ZIP on a fresh machine is still to be demonstrated.
3. The WP evidence directories contain the analyzed C sources and recorded commands. Run each command in its evidence directory with Frama-C 32.1 and Alt-Ergo 2.6.4. The callee evidence contains the scalar lemma and stencil logs. Inspect the named propositions and warnings as well as the totals.
4. Run `python evidence/cosine-one-invocation-6asyt36h/check.py evidence/cosine-one-invocation-6asyt36h/initial.hex` for the measured initial grid. The capture record gives the compiler flags and the separate hashes of the shipped and instrumented source.
5. In the recorded WSL setup use `bash work/check-why3-floor-even.sh` for the Rocq realization, using the pinned Why3 release in the opam download cache and the recorded Coq and Flocq versions. Review both assumption lists after coqchk.

SHA256SUMS.txt covers the packaged files. Archived diagnostics may include paths from the original Windows and WSL workspace. Publication and independent reproduction are separate from this local candidate build.
