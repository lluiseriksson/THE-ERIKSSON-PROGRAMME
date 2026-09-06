# Directionwise torus rectangle masks — bounded next diagnostic

Source adfef2b5b883a839e24b03ceedd118b32428dace, PRE-VALIDATION.
Template/test checkpoint 478c40e6f3b5bc896792a5a89187bcadc9c9f313.
This does not modify or append to the wrap/flat cold gate already running.

First preserve and independently verify that cold result. If it passes and
the SAME runtime ec5e95d70d1c survives, it may be reused for this separate
bounded HOT before final disconnection. Never call this HOT evidence cold.
If the cold gate fails, this diagnostic stays queued: repair only that error.

## Endpoint

For an active site x of the actual rectangular region, h=Int.toNat(m_i),
k=(x i).val, positive sides and the ORIGINAL non-strict fit m_i<=N:

- outgoing bond is retained iff h=N OR k+1<h;
- incoming bond is retained iff h=N OR 0<k.

The full-side case retains wraps, including N=1. Proper sides give integer
boundary masks only in that direction. Other coordinates need no strict fit.
The actual incoming target is identified using FinBox.shift_shiftBack.
No source/target orientation, spacing, coefficient or operator is replaced.

The two natural modular lemmas are copied exactly into the physical draft.
Run their Mathlib-only repro FIRST, then the physical prerequisite and draft.
Expected audits: two names in the repro, four in the draft. Repeated arithmetic
names in separate invocations are intentional, not extra physical outputs.

## Gates before launch

The templates deliberately have None for parent archive, independent review
commit/hash and parent production olean. main() must reject them before I/O.
Fill only from the actual preserved cold report; select its wrap olean hash,
verify the report source15e776db59c051571f79e47974acc2fbf597f715, PASS and
exact outer archive. The full independent report is hash-pinned, so the other
parent production output is not being silently accepted from an unreviewed run.
Hash every actual runner/reader from Git blobs after pinning. Verify exact
template instantiation, not a fresh untested handwritten replacement.

Physical prerequisite: YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion.
Caps:600s prerequisite;120s each repro/draft and small read-only check.
Actual stages:base_head,mathlib_pin,lean_version,lake_version,clean_before,
mathlib_repro,physical_prerequisites,physical_draft,clean_after.
No project source is changed in the retained checkout. First-error stop.
Preserve the original archive and its independent verdict before any repair.

Templates:
- tmp/colab_neumann_rectangle_directional_masks_hot_template.py
- tmp/verify_neumann_rectangle_directional_masks_hot_template.py
- scripts/test_neumann_rectangle_directional_masks_hot_template.py

Latest local instrumentation test:exit0/0.2865275s/24674304 observed peak RSS.
Actual producer AST matches nine reader stages, source audit declarations
match the two/four exact names, arithmetic repro body is unchanged.
Synthetic valid1/rejected11/preserved_failure1; compiler evidence NONE.
The initial AST checker selected every tuple loop instead of stage/path;
its local assertion caught that instrumentation bug and was narrowed before
publication. No Colab run was spent on it.

## What this does NOT solve

No physical carrier choice is produced. No original full-side input is
excluded. This is not a mixed-boundary image Green formula, reflection
covariance of full Eq246, the full-lattice point-source equation, a regional
right inverse, uniform physical B0, or attainment of window15.
The next consumer must combine these ACTUAL masks with the already checked
flat action, then separately justify its chosen reflection/periodic geometry.
20/41,TermSource0,window15 not attained,Clay<0.1% remain unchanged.
