# CMP89 (2.46) finite solution-cycle cold evidence

- Status: `PASS`
- Runner revision: `cmp89-eq246-solution-cycle-cold-v1`
- Source checkpoint: `e9f8f326262588c2c12ee98daa8e276cb0b63001`
- Runner commit: `2cdc9b070b6b28f098f81c2bd0a36d5e6d3915bd`
- Launcher commit: `0aa5975c28beeb282eb70b8d27143d0bf72a7371`
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`
- Canonical payload SHA-256 printed by Colab: `A60A01F48BF9583E2770BF693CC3A72A5A0A7FDA6EE7DB48DEA71035572E061A`
- Downloaded `evidence.json` SHA-256 (including its terminal newline): `24E07B3051D4A0F79C7FC7935CA9C12D0F00D7E943270A111D7501905ABA1D56`
- Evidence archive SHA-256: `48B80CF2BBF344EE28FB5CC70E59078ECE4B1A5E8851C3900D9EDF1E0A38A22E`
- Executed notebook SHA-256: `D690DA6D5811BA3D0637EADF305FDA7776E0034F19EBB5FA4A8A9591EDFB88EA`

The archive was downloaded from the retained Colab runtime and verified on
Windows before sealing.  The generic fail-closed verifier accepted all pins,
four source blobs, eighteen records and the exact four-stage queue.

Stage results:

- `alias_precision_cycle_focal`: exit `0`, `1328.153 s`, `8504` jobs
- `alias_precision_cycle_audit`: exit `0`, `8.551 s`
- `fine_point_source_solution_cycle_focal`: exit `0`, `56.970 s`, `8504` jobs
- `fine_point_source_solution_cycle_audit`: exit `0`, `7.658 s`

The three audited declarations use only
`{propext, Classical.choice, Quot.sound}`.  This evidence does not prove the
complete-integrand periodicity, boundary seam, contour deformation, CMP89
(2.42), uniform physical `B0`/`delta0`, attainment of window 15, a new
terminal field, or a `TermSource`.  Counters remain `20/41` and
`TermSource = 0`.
