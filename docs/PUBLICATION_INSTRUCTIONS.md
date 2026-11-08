# Publication instructions

The exact original RC2 archive is intentionally not in this public distribution because its historical path identifiers were redacted in the distributed evidence. See [provenance](DISTRIBUTION_PROVENANCE.md) for the distinction. The published RC2 ZIP is a path-redacted derivative and is not byte-identical to the frozen original.

1. Confirm that the complete repository tree is present on `main`, including `.github/`, `rc2/`, `figures/`, `release-assets/`, and `supplements/`.
2. Check the tracked source, figures, and evidence. Run `sha256sum -c docs/RELEASE_ASSET_SHA256SUMS.txt` from repository root.
3. Open **Actions > Publish RC2 public distribution > Run workflow**. It checks the ZIP bytes, creates the `heat-rc2-20261108-public` tag and attaches three release ZIP assets. It refuses to overwrite an existing tag.
4. Keep the two post-RC2 supplemental archives separate from RC2 release assets. The release notes distinguish theorem scope, measured runs and trust boundaries.
5. The unchanged original RC2 archive remains separately preserved. Its raw historical paths require privacy review before any independent public deposit.

No new mathematical proof or independent clean-build claim is implied by repackaging or publication.
