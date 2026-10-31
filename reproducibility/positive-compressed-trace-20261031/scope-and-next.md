# Scope of unit051

Target: derive the positive finite compressed trace/rank inequality, not the
full physical average-weight conclusion. For a finite real test subspace S,
T is an ambient linear map and L maps to finite output F. Compression is
actually defined as S.subtype.adjoint * T * S.subtype. Its inner identity
and positivity are proved; invariance T(S) subset S is not a premise.

With nonnegative quadratic form on S and c>=0, coercivity on S intersect
ker L implies c*(dim S-dim F)<=trace(compression). The proof constructs an
orthonormal basis of the actual kernel, extends its range, compares the
nonnegative complementary diagonal sum, and uses actual rank-nullity.
The kernel dimension and trace bound are not structure fields.

Failure072 at b87f6e562b7a0b9a4f7b8bcc868c5e50d3cb9b67 is preserved in full.
Only the final finset/subtype sum transport failed elaboration. The correction
at e9fb5a4f6d9263c805a032d8e2be5078c484455c explicitly supplies the function
and symmetry of Finset.sum_coe_sort. No theorem premise, conclusion or six
oracle endpoint criteria changed. Unused finite-dimensional section-instance
linter warning is not a proof failure. Driver072b was prepared, not executed.

Single next question after terminal reproduction: compose this generic theorem
with the actual normalized transverse physical strip, derive positivity from
flatGaugeHodgeK0_nonnegative_right plus componentwiseWeightedRepair_nonneg,
derive a strip orthonormal basis via pinned OrthonormalBasis.span, and prove
the local derivative-kernel lower estimate from the existing norm-ratio limit
and original upper-quadratic penalty hypothesis. Then transport unit049's
exact energy sum to compressed trace and add the existing multiplier bound.
The complete physical rank obstruction is not yet formally verified here.

Nonnegative form on S suffices; no need for positivity on all ambient E.
No symmetry premise is needed for this real quadratic trace comparison.
Do not infer T-cP_kernel is nonnegative. Unit050 refutations prohibit silently
replacing the upper-quadratic penalty with Lipschitz/C1 regularity alone.

Classical linear algebra, no original-priority or independent-review claim.
Keep the grouped coarse-information dossier; no new PDF, small paper,
AIRR deposit, licence, external model assessment or physical mass-gap claim.
PR29 stays20/41,TermSource=0. Frozen public AIRR v3 is unchanged.

Pinned API inspected for next composition: OrthonormalBasis.span h s returns an actual basis on span(s.image v), and span_apply identifies each basis value with v i. With s=Finset.univ its finite-image span equals the range span; no new orthonormality certificate need be introduced.
