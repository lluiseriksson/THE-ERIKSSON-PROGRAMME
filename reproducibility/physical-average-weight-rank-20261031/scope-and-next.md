# Unit052: actual finite physical average-weight rank composition

Scope: finite flat unit-spacing lattice, d>=2 represented by distinct i,j,
Nc>=2, nonnegative componentwise weights, R<n, arbitrary finite normed output
F, C(0)=0, Frechet derivative L at zero, local quadratic upper penalty and
local coercivity on the actual divergence-free sector. K, delta and radius
are finite-lattice quantities; no uniformity across lattice sizes is assumed.

Intended derived conclusion, with q=dim_R F and the actual spatial mean
b_ij=n^(-d)*sum_x w(i,(x,j)), is

    c*(2R-q) <= 2*(1+b_ij)*sum_(r=1..R) |stdAddChar(r)-1|^2.

No pointwise cap, assumed low-band dimension, assumed orthonormal family,
supplied kernel coercivity, supplied positivity or trace comparison appears
in the final theorem. The actual subspace is constructed from the normalized
physical fields already verified in unit049. Its divergence zero is derived
by span containment in the actual constraint kernel. Hodge and nonnegative
weighted repair positivity come from their actual existing operator lemmas.
An actual basis of the span is made from Basis.span, with orthonormality
proved from the original family's inner products, and the compressed trace
is identified with the exact basis energy sum. Unit051's generic bound is
then applied after deriving kernel coercivity from local nonlinear data.

The kernel calculation retains the original upper-quadratic penalty. For
v in ker L, the existing Frechet norm-ratio limit gives a vanishing normalized
penalty. Local coercivity at small t*v is divided by its positive squared
norm and passed to the limit. The v=0 case is handled separately. No bound
on K shared across different n is needed. Unit050 prohibits replacing this
upper-quadratic hypothesis with C1/Lipschitz regularity alone.

This removes the need for an externally supplied pointwise-cap comparison
in this NONNEGATIVE finite-flat class, if and when the new source passes.
It does not extend the result to arbitrary signed weights allowed by some
earlier pointwise-cap theorems. No interacting/continuum Yang-Mills hypothesis
is removed. Actual finite operator statements do not establish a physical
mass gap. PR29 remains20/41,TermSource=0.

Single next question after terminal reproduction: derive a quantitative
multiplier bound using existing stdAddChar_centered_bound and conclude output
rank divergence for fixed c>0 when (1+b_ij(n))/n^2 tends to zero. That
asymptotic conclusion remains unformalized in this unit's target. Keep the
same grouped coarse-information dossier and do not create a small utility
paper or duplicate AIRR deposit. Frozen public AIRR v3 stays unchanged.

Primary background: Spielman's author-hosted Spectral Graph Theory chapter,
sections16.3.2 and16.5, https://www.cs.yale.edu/homes/spielman/PAPERS/SGTChapter.pdf,
consulted2026-10-31, gives classical weighted quadratic forms and variational
spectral mechanisms. Pinned Mathlib Basis/Basic.lean at
07642720480157414db592fa85b626dafb71355b, blob
b553f746e683d8f5abfea1ce58decfcbec217ba7, supplies Basis.span and
Basis.coe_span_apply. These are background/implementation sources, not a
claim that this exact repository theorem is novel or independently reviewed.
No original-priority claim is made. Proof correctness, originality and
physical relevance remain distinct. New source has no inherited verdict;
only exact source, successful reports and paired output hashes can close it.

Failure074 atbd013f56 is preserved in full. Its two diagnostics concerned additive monotonicity argument order and rewriting the named physical span into the actual basis span. Corrected sourced03ab7ef supplies add_le_add (le_refl _) and explicitly changes the trace type to the constructed span. Intended hypotheses, conclusion and six oracle criteria remain identical. Prepared074b was not executed.
