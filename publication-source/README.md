# FluxWitness 1D heat benchmark

The RC2 archive contains the theorem, sources, premise ledger and reproducibility instructions. Its SHA256 is d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0. The operator reported PROJECT_REPLAY_ACCEPTED with exit 0 for the fresh project-module replay using pinned local dependency objects. The raw replay log was inaccessible during figure packaging. Independent clean-dependency reproduction remains open.

**Figure 1.** The final cosine profile and the change from initialization across 400 cells in one instrumented C invocation after 223 Heun steps. The change panel uses units of 0.001.

**Figure 2.** Absolute difference between the captured final CSV and the numerically evaluated effective-diffusivity cosine reference at each cell center. Peak measured difference is approximately 7.02705 × 10⁻⁹. The dashed line denotes the conditional Lean bound of 7.05 × 10⁻⁹ for the rounded model given initial pointwise error at most 2.4854 × 10⁻¹⁶. The plot is an empirical comparison for this invocation.

PDFs are vector originals; PNGs are for online posting. To regenerate with Python, ReportLab and pypdfium2 (with Pillow), run `python heat_publication_figures.py FluxWitness-Heat-Conditional-20261108-rc2.zip figures`. The script checks the source archive hash before reading the data. The final reference curve is evaluated with Python math on binary64 values; the plotted discrepancy is an approximation.
