# Prepared bounded periodic transfer diagnostic

PRE-VALIDATION, not executed. Source3b0576aa1329025f815ebee0edd15666d6e432bd,
draft tmp/NeumannPhysicalPeriodicTransferDraft.lean, Git-blob SHA256
41b7242faf89cc5881f8f0b8b9eeef61035c1b946cc2a28def826b90832ab977.

Run only after the current image-seam cold gate finishes and its evidence
has been preserved and independently verified. Do not start parallel Lean.
Use the retained diagnostic checkout /content/hrpoly-neumann-boundary-orbit-diagnostic-v2
at108f30f954e3d807f16c4264fac56f4814c65ea4, not the immutable cold checkout.
The explicit NeumannActualCommonBlockTranslation prerequisite is incremental
and bounded to120 seconds; the proof is separately bounded to120 seconds.
Missing prerequisites must not silently become another cold rebuild.

Runner scripts/colab_neumann_physical_periodic_transfer_hot.py,
Git-blob hash86d1e45bf47c70d10581403c45c3a9275a9158e47b98f7450d263dfea890331c.
It takes --parent-sha256
6e9067b015a3fc4ef67801e07d3dc39f4076ed46371f4fed9917733ee33f23e7,
rechecks the preserved parent, exact checkout/pins and clean source, then
executes one incremental prerequisite and one draft. Stop on first error.
The independent reader is scripts/verify_neumann_physical_periodic_transfer_hot.py.
Syntax and source/base/pin/revision/two-name contract checks pass locally;
this is instrumentation checking, not compiler evidence.

Expected outputs are only endpoint transfer and integer-period image
transfer for the literal Green. No periodic tsum convergence, mixed-family
coverage, regional inverse, B0 or window15 is inferred. No counter change.
