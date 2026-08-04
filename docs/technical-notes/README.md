# Technical notes (not catalogue entries)

## os_reconstruction_uniform_v4.pdf
sha256 152011c10f1da904e94ad31506dc2a8dd287b86bca0d17b6e70f0674be487bb6
"Exact Diagonal and Mixed Reconstructed Correlator Decay from a
Dobrushin Window for Finite Coupled Z2 Slices" (Lluis Eriksson,
2026-08-04, 7 pages).  End-to-end finite-volume chain: intrinsic
Dobrushin comparison -> anisotropic rectangle -> band covariance ->
operator gap -> EXACT reconstructed diagonal and mixed correlators
(zero-time case included).  Produced by the parallel desk; its Lean
lane (reconstruction source sha256 a3089a96..., abstract bridge
1dd660dc..., builds 8191/8482, oracle 3054) lives in that desk's tree
state and is NOT reconciled with d3-closure (whose module is
YangMills/OS/OSReconstructionUniform.lean, sha 5445429f..., core 8481,
oracle 3017).  DECISION (owner, 2026-08-05, on the external
evaluator's recommendation): kept as a technical note, NOT submitted
and NOT a catalogue entry; the submission candidate is the OS-R-2
version (raw-measure identification + mixed correlators + the
machine-checked-landscape positioning of docs/OS-R-PRIORITY-COLLATION.md).
The public repository commit is the priority timestamp.
