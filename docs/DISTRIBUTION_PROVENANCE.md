# Public-distribution provenance

The original RC2 archive remains separately preserved, unchanged, with SHA-256:

`d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0`

The original ZIP contains a historical machine directory identifier that is outside the scientific proof content. To keep this public distribution free of names unrelated to the project, **only identifying path strings in selected historical logs and JSON diagnostics were redacted**. The original RC2 README's machine-specific workspace path was replaced with a placeholder. The theorem and C source files are not changed. The initial public-distribution README and publication instructions were rewritten. No Lean build, C solver run, or formal-verification command was rerun when repackaging.

Because the archived bytes changed, the public RC2 archive has a **different SHA-256** and must not be represented as the frozen original. The public manifest covers the public archive's extracted files. The three archive log/JSON redactions were:

- `rc2/evidence/lean435-benchmark-native-half-20261105/BenchmarkNativeHalf-20261106-224528/result.json`: 103 path-text substitution(s)
- `rc2/evidence/repair-20261023-034345/heat-execution-trace-check-20261030-020013/result.json`: 3 path-text substitution(s)
- `rc2/evidence/why3-floor-even-c7JKUEAm/check.log`: 3 path-text substitution(s)
- `rc2/README.md`: 1 path-text substitution(s)

The public release's figure-publication ZIP excludes the nested original RC2 ZIP. Its figures and figure generator remain present. This is a distribution-format change, not a new proof claim.

The wider-initialization and nominal-reference supplements are post-RC2 and were not part of the frozen proof release. Their recorded results should not be described as independent clean-machine reproductions.
