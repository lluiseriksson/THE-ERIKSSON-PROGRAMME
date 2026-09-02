# CMP89 (2.46) complete-integrand periodicity and seam cold seal

- Runner revision: `cmp89-eq246-integrand-periodicity-seam-cold-v1`
- Source checkpoint: `dec1cb163d7d0d2dd5d79270f6591db68a17ec5f`
- Runner checkpoint: `81ddb7749aaf4b79275c2a870a43d03ecda11337`
- Launcher checkpoint: `e58f3b31d905dbb14545d033a8951153daaa691e`
- Opened UTC: `2026-09-02T13:03:29.327450+00:00`
- Closed UTC: `2026-09-02T13:30:37.094764+00:00`
- Final status: `PASS`

The fresh Colab Pro+ CPU/high-RAM project restored no project
`.lake/build` graph.  It verified the official Lean `v4.29.0-rc6` asset,
Mathlib commit `07642720480157414db592fa85b626dafb71355b`, all four source
blobs, and both textual guards.  The four stop-on-first-error queue stages
all exited zero:

- `integrand_periodicity_focal`: `1399.1155626520003 s`
- `integrand_periodicity_audit`: `8.769811724999272 s`
- `boundary_seam_focal`: `30.955578224999954 s`
- `boundary_seam_audit`: `9.023212584000248 s`

Hashes verified on Windows:

- canonical evidence JSON:
  `51AAB3A1C51923212D1D64CE00298E4A979C93344F7116733FC47BBBA65347D7`
- downloaded archive:
  `2E3C1A82D9A274539FFD2D17A6A72B75E1A7D6A9E888AAE10454663DD2A244A3`
- recovery notebook:
  `B942B13247230607C80CF66999909AC959FB70CDCD74468D49B5AB4A7FFB2B64`

The browser tab containing the originally added cold-run cell was lost while
Colab retained the runtime.  The primary durable evidence is therefore the
runner-produced archive and its extracted JSON.  The preserved notebook is
explicitly a recovery transcript: it contains the read-only cell that
reported `FINAL_STATUS=PASS`, all record exit codes and the archive hash, plus
the one-shot download cell.  It is not represented as the lost original
runner transcript.

This seal proves only periodicity and the Brillouin-face boundary seam of the
complete CMP89 (2.46) physical fine-to-fine integrand.  It does not prove a
contour shift, the four-coordinate telescope, CMP89 (2.42), uniform physical
`B0`/`delta0`, attainment of window 15, a terminal field, or a `TermSource`.
Counters remain exactly `20/41`; `TermSource = 0`.
