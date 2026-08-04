# (52) Response to the 5.18/10 review

Status: formal and documentary revision for independent reassessment; not a
self-issued score.

The 5.18/10 review credited the integrated finite-volume argument but still
identified a formal mismatch: the mixed-correlator statement was present only
as a paper-level consequence, while the frozen Lean endpoint remained
diagonal.  V4 closes that precise mismatch without adding or sharpening an
analytic estimate.

| Review point | V4 response |
|---|---|
| Mixed decay was not a named formal endpoint | `TransferGap.lean` now defines `mixedConnCorr` and proves `VacuumTransfer.mixedConnCorr_eq` and `mixed_clustering_of_gap`. |
| The zero-time case can be silently mishandled | `mixed_clustering_of_gap` treats `n = 0` separately, using `norm_one_sub_vacuumProjection_le`; it does not identify `P^0-Pi` with `(P-Pi)^0`. |
| The reconstructed theorem did not expose arbitrary pairs | `OSReconstructionUniform.lean` now defines `reconstructedMixedConnCorr`, proves its exact equality with `mixedConnCorr`, and proves `reconstructedMixedConnCorr_decay`. |
| The headline theorem remained diagonal | `os_reconstruction_uniform_gap` now returns both the diagonal decay statement and the arbitrary-pair product-norm bound. |
| Source presence might be confused with verification | The changed target and its dependency target were built in a fresh Colab CPU/high-RAM runtime, and the exact local oracle source was run exhaustively in four chunks.  Exact source, log, counter, and `.olean` hashes are recorded in the verification manifest. |

The formal increment is deliberately narrow.  The mixed inequality is a
Cauchy--Schwarz consequence of the already checked operator-gap estimate; v4
does not claim a new Dobrushin window, a sharper exponent, or a stronger
finite-volume analytic input.  It does make the paper's advertised observable
family agree exactly with named, checked declarations.

The revision still proves no thermodynamic limit, boundary-condition
independence, continuum theory, Wightman reconstruction, or Yang--Mills mass
gap.  Those are genuine mathematical extensions and were not introduced by
editorial or interface changes.

No score above 5.18/10, including the requested threshold of 6/10, is
self-certified.  The v4 PDF and frozen evidence object are prepared for an
independent rescore.
