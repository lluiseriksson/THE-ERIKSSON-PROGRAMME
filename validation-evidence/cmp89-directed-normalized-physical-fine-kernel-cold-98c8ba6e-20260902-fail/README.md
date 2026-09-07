# CMP89 directed normalized physical fine-kernel cold failure

- runner revision: `cmp89-eq246-directed-normalized-physical-fine-kernel-cold-v1`
- runner commit: `313d0b572f6cdf7a2a3ec06788a168e0a589c556`
- launcher commit: `e34d2839c06bc04b71494c2585455d0e84acfb66`
- exact source: `98c8ba6e6a53c01442f6b43bd69bd82d81a746df`
- result: `FINAL_STATUS=FAIL`
- first failing stage: `directed_normalized_physical_fine_kernel_focal`
- focal exit: `1` after `965.589 s`
- archive SHA-256: `380dd0572d6fefce406b0a7401f71763314e6d7a3e84488a245b84f778c6a1c9`
- evidence payload SHA-256: `91d76b27c5c892029468a413ad15bd09da491f5d10909477a48d4e04a5384ed7`
- executed notebook SHA-256: `6c7b18b010c8c37626c4425e99213fa1009464f654b24fae352b74cd7d8f3170`

The fresh Colab CPU/high-RAM checkout reached `8523/8524`. The first and
only failing target was
`YangMills.RG.BalabanCMP89Eq246DirectedNormalizedPhysicalFineKernel`; its
audit did not run.

At line 71, `rw` could not see the displacement-scaling pattern through the
local `let displacement := ...` retained in `hbound`. The theorem statement,
rate conversion, hypotheses and bound constant are unchanged. The repair is
restricted to exposing that local definition before applying the already
proved scaling identity. PRE-VALIDATION remains in force and this archive is
not compiler evidence for the repair.

The fail-closed local verifier accepted the source and environment pins, both
source blobs, the single failing queue record, duration, exit code, evidence
payload and archive hash.

Counters remain `20/41`, window 15 remains compatible but unattained, and
`TermSource = 0` remains exact.
