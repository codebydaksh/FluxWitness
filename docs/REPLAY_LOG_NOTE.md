# RC2 Lean replay log: provenance and path handling

The user's archived local replay log was supplied after the initial repository kit was assembled. The original is preserved by the submitting author and is **not included in this public-facing repository kit** because it contains local Windows paths.

- Original SHA-256: `458eb46d557477a677fcc01285179ec76f3d53fe75d90de89331fc78b47fe441` (42,522 bytes).
- Public path-redacted copy: [`replay-public.log`](replay-public.log). SHA-256: `253ad7dbf4b1ac1949b55be2a15f50d17e0fdcc22cc9dd88fe6d3bf53934b7d4`.
- Transformation: 114 occurrences of the local absolute replay-workspace path were replaced with the literal prefix `replay-root/`. The remaining lines were not edited.
- Log contains `ReleaseAudit` output for six RC2 declarations, listing only `propext`, `Classical.choice`, and `Quot.sound`. It also includes warning diagnostics; the original file does not contain a process exit code, so it is **not by itself independent evidence that the command exited 0**. The user's runner report separately claims exit 0.
- This is historical evidence, not a fresh independent clean-clone proof run.

The canonical frozen RC2 ZIP and its original SHA-256 `d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0` remain unchanged. If the unmodified original log is released separately, review those paths first and label it as raw.

**Distribution notice:** The raw original log is not included in this repository. The path-redacted public log preserves the reported axiom declarations and nonzero/zero status evidence from the recorded replay.
