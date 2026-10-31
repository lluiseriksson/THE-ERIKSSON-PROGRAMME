# Positive compressed trace/rank comparison

Verified proof source e9fb5a4f6d9263c805a032d8e2be5078c484455c. In a finite real inner-product space,
nonnegativity of x -> <x,T x> and c||x||^2 <= <x,T x> on an actual
submodule H imply c*dim(H)<=trace(T). An actual orthonormal basis of H
is embedded, its range extended to an ambient orthonormal basis, and the
remaining nonnegative diagonal sum compared. No kernel dimension or
trace comparison is supplied as a certificate. Rank-nullity then gives
c*(dim(E)-dim(F))<=trace(T) for the kernel of arbitrary linear L:E->F,
provided c>=0.

On an actual submodule S, the defined compression is
S.subtype.adjoint.comp(T.comp S.subtype). Its inner product is proved
equal to <x,T y> in the ambient space. Nonnegativity only on S suffices.
Consequently coercivity on S intersect ker L implies
c*(dim(S)-dim(F))<=trace(compression). The ambient operator need NOT
preserve S; no symmetry or positivity of T-cP_kernel is assumed.

Two fresh own Colab Linux clones073/073b at the SAME proof source passed
six exact standard-axiom reports and all execution steps. Compiled target,
raw oracle and LF source-manifest hashes match. Actual mutations rejected3
and positive evidence accepted1 in normal and Python-O validator modes.
Pinned Mathlib cache used, not a full Mathlib source rebuild. No Windows
Lean/Lake/oracle, GPU or independent scientific review. All owned runtimes
released and own notebook tabs closed; captures and raw reports retained.

Failed072 source, exact diagnostic and one-line patch are preserved. The
failure was an elaboration of the final finset/subtype sum transport; the
fix supplies its function and symmetry explicitly without altering the
theorem or oracle criteria. Prepared072b was not executed.

This closes the GENERIC positive compressed trace/rank bridge, not the
full physical average-weight theorem. The actual local derivative-kernel
estimate, physical positivity, strip orthonormal-basis trace identification
and quantitative multiplier composition remain to be formally connected.
Existing actual strip and energy sum from unit049 are separately verified.
Retain the original quadratic upper penalty; unit050 rules out silently
replacing it by continuity/Lipschitz/C1 alone. Full average-weight formal
closure and any physical hypothesis elimination are NOT claimed here.

Classical trace/rank-nullity methods; pinned primary Mathlib source and blob
context are recorded. No original-priority claim, new PDF, paper, deposit,
licence or model assessment. Keep the grouped coarse-information dossier.
Frozen public AIRR v3 unchanged; PR29 remains20/41,TermSource=0. No physical
mass gap or interacting/continuum result. Single next question is the actual
physical derivative-kernel/strip composition in scope-and-next.md.