# CMP89 Eq. (2.46) domain/cycle/uniqueness cold seal v2

- Result: `PASS`
- Source checkpoint: `df364a3c629004ff7ca1062247cfe488b0579f2e`
- Runner commit: `928f59ee5c27e1bf9c1679b58a1a6be48eae75b5`
- Launcher commit: `8c9faa77`
- Runner revision: `cmp89-eq246-domain-cycle-uniqueness-cold-v2`
- Runtime: Colab Pro+ CPU/high-RAM, `50.99 GiB`
- Opened: `2026-09-02T11:33:52.175083+00:00`
- Closed: `2026-09-02T11:55:38.001147+00:00`
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`
- Lean toolchain asset SHA-256:
  `BF3E0A4025E47A0BEA9ED907D12DCCD3D3590B1D8AD6C55A915298B01AD9D3E`
- Evidence JSON SHA-256:
  `04D9B70CDC8896198DC9AF8E5EBC374AA8C6A08F32FC85B0D7B94EB5C916E067`
- Archive SHA-256:
  `2E6DE0A469FD2770D39BA05732A835F848288E59FA1BE5B9BE13195038F48226`

The fresh checkout restored no project `.lake/build` graph.  The runner
verified all six source blobs and both lightweight guards, materialized the
exact Mathlib pin, and completed the six-stage stop-on-first-error queue:

1. `FullSolutionDomain` focal: exit `0`, `1106.121 s`;
2. `FullSolutionDomain` audit: exit `0`, `8.169 s`;
3. `AliasCycleTransport` focal: exit `0`, `36.883 s`;
4. `AliasCycleTransport` audit: exit `0`, `7.980 s`;
5. `AliasPrecisionUniqueness` focal: exit `0`, `10.918 s`;
6. `AliasPrecisionUniqueness` audit: exit `0`, `6.398 s`.

The strict audit parser saw the expected eight declarations and accepted
only the allowlist `{propext, Classical.choice, Quot.sound}`.  The local
fail-closed verifier accepted the complete six-stage payload.

The browser tab that contained the ephemeral executed launcher cell was lost
while Colab was reconnecting to the still-running runtime.  The executed
notebook therefore was not preserved, and this directory deliberately does
not relabel an unexecuted source notebook as that artifact.  The downloaded
fail-closed archive and its extracted `evidence.json` are the preserved cold
seal evidence.  The runtime was disconnected and deleted only after the
archive passed local verification.

This seal retires only the six PRE-VALIDATION notices for the three focal/audit
pairs.  It does not prove complete-integrand periodicity, contour deformation,
CMP89 (2.42), uniform physical `B0`/`delta0`, attainment of window 15, a new
terminal field, or a `TermSource`; counters remain `20/41` and
`TermSource = 0`.
