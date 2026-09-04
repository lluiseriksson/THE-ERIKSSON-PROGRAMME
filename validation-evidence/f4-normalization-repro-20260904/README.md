# Auxiliary F4 normalization repro, not a cold seal

Runtime `bc8fae8b949d`, Colab Pro+ CPU/high RAM, 2026-09-04 UTC.
The active source-flow foundations cold checkout was not changed by this
project-free repro. No local Lean/Lake execution occurred.

Archive SHA256 (matched Colab and Windows after browser download):
`3F90415764AF3147A3663EA87F818210ADA96050DD71C36A6EBC2A3EA617B62D`.
Eight members: the two source versions, two logs, two measured result JSONs,
the earlier pre-Lean launch failure transcript and the member-hash manifest.

1. First launch: `FileNotFoundError: 'lake'`, before any Lean child. Wrong
   outer toolchain bin path. The actual nested path was measured from the
   active cold Lake process; no mathematical conclusion from this launch.
2. Original repro at `0ac5a1760795b6c25aa8880a3f9bdc30935c75c6`:
   exit 1 in 12.915449988s. First error at line 24: `add_le_add_left` put
   the common summand on the opposite side. Its failed declaration printed
   `sorryAx`; the repro is rejected, not compiler evidence.
3. Corrected repro at `995370c162c80694029242785925e7bae08476f4`:
   source blob SHA256
   `B709E6376B505D55846ACD6D255A56DB06D2A817B40F671DAC296A0C568A1F4F`.
   Only the sum step changed to `add_le_add (le_refl _) hs`.
   Exit 0 in 11.700545847s. Both `split` and `retain_inverse_square`
   printed exactly `{propext, Classical.choice, Quot.sound}`.
   Log SHA256
   `B17B5D8C6161C6E24F8234781D3115194E758381B7BFE653EFA0D3A397996A60`.
   Unused/unreachable tactic warnings remain; no warning-free claim.

This validates elementary real inequalities in an auxiliary hot repro only.
It does not bound the literal full-G amplitude, instantiate a source-flow
dictionary, produce physical B0, attain window 15 or change 20/41.
