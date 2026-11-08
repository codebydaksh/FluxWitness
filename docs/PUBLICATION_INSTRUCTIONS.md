# Publication instructions

1. Import the full prepared distribution tree, including `rc2/`, `figures/`, `supplements/`, and `release-assets/`.
2. Verify all five distribution ZIPs: `sha256sum -c docs/RELEASE_ASSET_SHA256SUMS.txt`.
3. Review the trust ledger, proof sources, diagnostics, and provenance before making the repository public.
4. Only after all files are present, manually run **Actions > Publish RC2 public distribution**. It creates a distinct release and refuses to overwrite existing tags.
5. Keep wider-initialization and nominal-reference results outside the original frozen RC2 claim.

The untouched original RC2 ZIP remains separately preserved. Repackaging is not a new proof run. A fresh source build using pinned dependencies remains an independent reproducibility check.
