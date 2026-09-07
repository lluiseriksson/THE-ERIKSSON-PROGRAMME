# Image-seam promotion — PRE-VALIDATION

Five source modules and an eleven-declaration audit are prepared. They are
not cold-sealed, and no PRE-VALIDATION marks have been retired.

The read-only gate `scripts/check_neumann_image_seam_promotion.py` compares
against Git blobs at efdbce22459e76d05a728f912a786d7f571dad3d. The only
permitted changes are mapped production imports, the explicit unverified
production header, moving print-axiom commands to the audit, and terminal
blank lines. Statements, hypotheses, constants and proof bodies are unchanged.
The gate passed in 0.2283036 seconds with observed peak RSS 18001920 bytes.
This is textual equivalence evidence, NOT compiler evidence.

## Evidence gate before cold promotion

Endpoint transfer HOT evidence is durable in Addendum 1201. The subsequent
physical image-seam HOT result is PASS in retained Colab, source
970356bfc58ec2ca9ba94163be952d382c0689c9, three allowed-trio audits.
Its archive is /content/neumann-physical-image-seam-hot-v1.tar.gz (59473 bytes),
SHA256 cd7a66477087916e59c54bf0f6d995810ab838d10eedb7168ec3a7fc04e12977.
Local download and independent recursive verification are still pending.
Browser download requests emitted no error but produced no local file;
clipboard transport yielded empty bytes and was rejected by the hash gate,
with no output file written. Do not repeat the scientific calculation.

Next: preserve that archive and run verify_neumann_physical_image_seam_hot.py
against all preserved parents. Then prepare a fresh-clone cold gate of the
six exact paths listed in NEUMANN-IMAGE-SEAM-PROMOTION-PATHS-20260907.txt.
No restoration of the project build outputs in that cold checkout.

## Cold instrumentation prepared, not launched

Source checkpoint: 0f43fbdc51650fb2e8d77282d1c3af18b7f406f0.
Runner: scripts/colab_neumann_physical_image_seam_promoted_cold.py.
Independent reader: scripts/verify_neumann_physical_image_seam_promoted_cold.py.
Both pin the six production Git blobs, five output objects and eleven names.
Their source/blob/name/command contracts agree (read-only AST check,
0.0944694 seconds, observed RSS 14905344 bytes). The reader synthetic
self-test accepts its fixture and rejects eight corruptions; the pinned
axiom gate accepts two fixtures and rejects nine (0.1260639 seconds,
observed RSS 16736256 bytes). None of this is a compiler run.

Queue: lake build YangMills.RG.NeumannPhysicalImageSeam, then lake env lean
YangMills/RG/NeumannPhysicalImageSeamAudit.lean. Only Colab CPU/high RAM.
Keep the launch blocked until the pending HOT archive is durably preserved
and independently verified. The pinned original cold bootstrap is reused;
no extra workflow dispatch, no local Lean, no project build-cache restore.

## Scope that survives promotion

The literal physical Green is used. The fine/block equality c*m(mu)=L^j*B
is retained. Convergence is supplied separately from totalized-tsum
reindexing. Lower/upper ghost values are proved without exchanging sums.
Only all-reflecting families are covered. Mixed FULL directions, the
full-lattice point-source equation, operator/sum exchange and regional
inverse identification remain open. 20/41, TermSource=0, window15 not attained.
