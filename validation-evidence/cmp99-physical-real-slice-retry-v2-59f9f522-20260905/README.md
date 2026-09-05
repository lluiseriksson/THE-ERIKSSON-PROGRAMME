# Physical real-slice retry v2 — verified diagnostic PASS

Source: `59f9f522f3f731ac8a6270ac5c3ae719b1b201f6`.
Notebook vehicle: `c5400201b96d4b5cc782906255b1cd130c9c419d`.
CPU/high RAM Colab, host685dabaa0a79, start2026-09-05T13:07:22.137527Z.
Launcher child diagnostic exit0,2299.775889465s; archive verifier exit0.
No project build-cache restoration. The result remains explicitly
`cold_seal=false`: four draft declarations, not a promoted production seal.

Outer archive SHA256 (observed in Colab and matched after browser download):
`ea1fbf70419d803d4707fc452e0cd2b8ceca404514aeae02e96e0d0420d33286`.
Inner archive SHA256:
`4981054f53a473c7722a6ea475feaa6993e878074b7ec1cfc7bbe28266fb8f50`.

The downloaded pinned verifier initially stopped on Windows with
`ValueError: CONTRACT=queue`: importing the runner used Windows pathlib
to construct expected Linux `/content` command paths. This was an observer
portability defect, not a Lean failure. The original archive and helpers
are retained byte-for-byte. `scripts/verify_physical_retry_v2_posix_adapter.py`
normalizes only these expected command paths and expected ROOT/EVIDENCE;
it changes no archive bytes, source hashes, log text, axioms or exit codes.
The immutable verifier plus its seven adversarial tests then passed locally:
18 records, four exact public axiom sets, both actual output files hashed.
Local verification0.06426s, peak26,853,376bytes, one process and no Lean.

Measured child stages:

- Mathlib repro exit0,3.709982501s.
- Physical prerequisites exit0,2114.319442158s.
- Four-theorem physical draft exit0,31.395923566s.
- Final source-clean check exit0,0.810481973s.

Actual archived output hashes:

- `SourceFlowPhysicalCarrierRepro.olean`:
  `320fdd029aa9657584f568db2e728871e146df1122abb0f38454be3b44a45ef1`.
- `SourceFlowPhysicalGreenRealSliceDraft.olean`:
  `21f0ed13d3d9ab04bf7908197c37ae9f8bfbee04eca232c7982e76250f6e8ec4`.

This verifies real-slice identities for the internally constructed physical
source-flow Green, the named site evaluation, and exact output Lie-fibre
norm. It does not prove regional inverse identification, derivative B0,
window15 attainment, or a terminal field.20/41,TermSource0 unchanged.
The runtime is retained only for the separately prepared bounded owner/point
diagnostic after this evidence has been preserved and verified.
