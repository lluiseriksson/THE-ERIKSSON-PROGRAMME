# CMP89 (2.46) complete-integrand one-coordinate contour shift cold seal

- Runner revision: `cmp89-eq246-integrand-one-coordinate-shift-cold-v1`
- Source checkpoint: `881a6de1c6c945161c65f9d9966319b17e386e4c`
- Runner checkpoint: `71fd94dd1afef8fe5657c3c6dcb3a5c709ad64f6`
- Launcher checkpoint: `da52b3a91de748042171e0e7d9624c8d9c827484`
- Final status: `PASS`

The fresh Colab Pro+ CPU/high-RAM project restored no project
`.lake/build` graph.  It verified the official Lean `v4.29.0-rc6` asset,
Mathlib commit `07642720480157414db592fa85b626dafb71355b`, both source blobs and
both textual guards.  The two stop-on-first-error queue stages exited zero:

- one-coordinate contour-shift focal: `1388.8042340870002 s`
- exact audit: `11.123912294000093 s`

Hashes verified on Windows:

- canonical evidence JSON:
  `1C313B1B51EC84DF22FCFF706D2299DFE377309F7B491E41D82CDD19B1B771DE`
- downloaded archive:
  `0B7267C0851EFA5C6C8F904B4C5AD33F7A1A757723D6DA19427FAC055852FDE0`
- recovery notebook:
  `636852CE9E3DDF672D36D445BA187A4E1BEB3408422FE81EA04E865FD61A9335`

The browser tab containing the original runner cell was lost while Colab
retained the runtime.  The runner-produced archive and extracted JSON are the
primary durable evidence.  The notebook is explicitly a recovery transcript:
it records the read-only recovery of `FINAL_STATUS=PASS`, both stage exit
codes and the archive hash.  It is not represented as the lost original
runner transcript.

This seal proves one coordinate of the complete CMP89 (2.46) physical
fine-to-fine contour shift.  It does not prove the four-coordinate telescope,
CMP89 (2.42), uniform physical `B0`/`delta0`, attainment of window 15, a
terminal field, or a `TermSource`.  Counters remain exactly `20/41`;
`TermSource = 0`.
