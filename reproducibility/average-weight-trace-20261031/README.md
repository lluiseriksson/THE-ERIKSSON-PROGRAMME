# Directional average weights: explicit transverse strip and trace bound

Unit047, 2026-10-31. Mathematical derivation on paper, NOT a Lean-verified
extension. Exact repository definitions inspected at main
8f1fb22eef72dbab56b0daba8cc604f91ca4df56. No new compilation, oracle, Colab
allocation, PDF, review, deposit or publication is claimed in this unit.
Keep this work in the existing coarse-information dossier.

## Statement and conventions

Let D>=2, Nc>=2, n>2R, R>=1, N=n^D. All norms use counting measure and all
differences use the repository's unscaled periodic forward shifts. Fix two
distinct physical directions i,j. Use the actual isometric real embedding
J:C -> SUNLieCoord Nc given by sunComplexPlane, supported on two internal
coordinates, and torusPhysicalEmbed in bond direction j. No desired low-band
dimension, orthogonality, trace bound or constraint is an input certificate.

For actual nonnegative weights w(k,(x,l)), put

    b_ij = (1/N) sum_x w(i,(x,j)),
    B = flatGaugeHodgeK0CLM + componentwiseWeightedRepairCLM(w),
    lambda_r = |exp(2*pi*I*r/n)-1|^2 = 4*sin(pi*r/n)^2.

Assume the SAME local observation hypotheses as the finite flat programme:
C(0)=0, C Frechet differentiable at zero with derivative L into a finite
real space F of dimension q, Phi(y)<=K||y||^2 for ||y||<delta, delta>0,
and for every sufficiently small divergence-free A,

    c||A||^2 <= <A,B A> + Phi(C(A)),   c>0.

K,delta and the neighbourhood radius may depend on n. Nonnegative repair
weights are retained here to make B positive semidefinite. Some older
pointwise-cap theorems also allowed signed weights; the present argument
does not claim to weaken those theorems over their full signed class.

Then the following PAPER-LEVEL bound holds:

    c(2R-q) <= 2(1+b_ij) sum_{r=1}^R lambda_r
            <= 8*pi^2*(1+b_ij)/n^2 * sum_{r=1}^R r^2.       (1)

Thus a fixed-D,Nc family satisfying (1+b_ij(n))/n^2 -> 0 must have output
dimension q_n -> infinity. Only ONE fixed transverse directional average
is needed. Individual repair weights in that channel can have arbitrarily
large peaks. A vanishing total nonnegative spatial average divided by n^2
also suffices, because the fixed number D^2 of channels bounds b_ij by D^2
times that total average. This statement has not yet been added to the
formal theorem inventory.

## Derived actual fields, not a supplied band

Write chi_r(x)=exp(2*pi*I*r*x_i/n). Define two actual real physical fields
for each 1<=r<=R:

    e_(r,0)(x,l) = 1_(l=j) J(chi_r(x))/sqrt(N),
    e_(r,1)(x,l) = 1_(l=j) J(I*chi_r(x))/sqrt(N).

1. They are actual PhysicalGaugeOneCochain values: J is precisely the
   two-coordinate sunComplexPlane from TorusPhysicalEmbedding.lean, and the
   direction/site placement is torusPhysicalEmbed through finBoxZModEquiv.
   Nc>=2 supplies two distinct internal coordinates. No Lie bracket is used.
2. The actual flat divergence is the backward difference in j by
   torusPhysicalEmbed_flat_div_apply. Since i!=j, both characters are
   invariant under that shift, so the divergence is ZERO.
3. The 2R fields form a real orthonormal family. J is a real-linear norm
   isometry, hence an inner-product isometry by real polarization. Summing
   conjugate character products gives N for r=s and zero for r!=s: for
   distinct r,s in {1,...,R}, the ratio z=exp(2*pi*I*(r-s)/n) satisfies
   z^n=1 and z!=1, hence sum_{t=0}^{n-1} z^t=0. The remaining D-1
   coordinates contribute n^(D-1). For r=s the real part of I is zero,
   so the alpha=0,1 pair is orthogonal. Division by sqrt(N) gives norm1.
   In particular E=span_R{e_(r,alpha)} has dimension exactly 2R.
4. The only nonzero actual componentwise gradient channel is (i,j).
   Its squared pointwise norm is lambda_r/N at EVERY site, for EACH
   alpha separately, because |chi_r|=|I*chi_r|=1 and J preserves norms.
   This is stronger than requiring constancy only after summing a pair.
   The actual shift lemma finBoxZModEquiv_shift includes wraparound.
5. Therefore the weighted energy of EACH e_(r,alpha) is EXACTLY
   lambda_r*b_ij. No pointwise domination of weighted by unweighted
   energy is being assumed. All other weight channels contribute zero.
6. Its flat Hodge energy is exactly lambda_r: the actual divergence is
   zero, and the actual unordered-plaquette curl identity counts the
   single (i,j) plaquette once. Equivalently use the already verified
   torusPhysicalEmbed_flat_hodge_eq_stencil. There is no extra factor2
   from ordered plaquettes, nor from the two internal coordinates.

Consequently the trace of the COMPRESSED quadratic form on E is

    T_E = sum_(r,alpha) <e_(r,alpha),B e_(r,alpha)>
        = 2(1+b_ij) sum_r lambda_r.                         (2)

Inhomogeneous weights can mix Fourier modes: B(E) subset E is NOT assumed.
The compressed form means P_E B restricted to E. Its trace is independent
of the orthonormal basis of E by ordinary finite real linear algebra.

## Tangent kernel and trace inequality

For v divergence-free with L(v)=0, differentiability gives C(tv)=o(|t|)
as t->0. Divide local coercivity at tv by t^2 for nonzero small t. Its
quadratic B term is <v,Bv> and the penalty is bounded above by
K||C(tv)/t||^2, tending to zero. Thus

    c||v||^2 <= <v,Bv>.                                   (3)

This uses a quadratic upper bound near zero, not a hidden assumption
that C factors through another observation. No uniform K is required.

Let H=E intersect ker(L). Rank-nullity gives dim H>=2R-q. Choose an
orthonormal basis of H and extend it to an orthonormal basis of E.
Each vector of the first part has B energy at least c by (3).
Each vector of the complementary part has nonnegative B energy: the
actual flat Hodge form and G*WG are both nonnegative for w>=0. Hence

    c(2R-q) <= c*dim H <= T_E.

If q>2R the first bound is simply nonpositive; it remains valid.
Combining with (2) and |exp(I*t)-1|<=|t| proves (1).
No eigenbasis of B, spectral comparison certificate, or invariance
of E under B is needed.

For any fixed R, the upper bound in (1) tends to zero if
(1+b_ij(n))/n^2 -> 0. Eventually it is less than c. Then
2R-q_n<1, and integrality yields q_n>=2R. Since R is arbitrary,
q_n tends to infinity. This is a rank divergence result, not the
volume-density lower bound of the earlier much larger coexact band.

## Refutation of the tempting pointwise-energy replacement

An average-weight bound DOES NOT imply

    <A,G*WG A> <= b_max ||G A||^2                         (FALSE)

even on actual divergence-free flat fields. Take D=2, n=4, Nc=2,
i=first direction, j=second direction. At each x_2 let the only nonzero
bond direction j have first internal coordinate

    f(x_1) = (1,-1,0,0),

with the other internal coordinates zero. Put w(i,(x,j))=4 if x_1=0,
and zero elsewhere, including all other channels. This field is
independent of x_2, hence its actual divergence is zero. The chosen
directional average is b_ij=1; all others are zero, so b_max=1.

The forward differences in x_1 are (-2,1,0,1), with squared sum6.
There are four identical x_2 rows, giving ||G A||^2=24. Weighted energy
is 4 rows * weight4 * difference-square4 =64, so 64>24. Its norm
squared is4*(1+1)=8 and Hodge energy is24. Even the proposed total
bound <A,B A><=(1+b_max)||G A||^2 fails: 88>48.

All these numbers are exact arithmetic derived from the definitions,
not an output from a local certifier. This explicit negative case is
retained so the invalid operator-domination route is not retried.

## Verification, originality and limits

This unit checks the paper derivation against the exact repository
definitions and records the explicit counterexample. It is NOT a new
Lean proof, two-clone reproduction, external review, or publication.
The checks in proof-audit.json distinguish every layer. The previous
quadratic construction was formally verified and merged in PR117;
none of its compiled hashes are inherited by this new derivation.

Classical background: the weighted Laplacian quadratic form and
finite-dimensional spectral methods are treated in Daniel Spielman's
author-hosted primary sources, consulted 2026-10-31:

- https://www.cs.yale.edu/homes/spielman/561/lect02-15.pdf, sections2.1-2.2.
- https://www.cs.yale.edu/homes/spielman/PAPERS/SGTChapter.pdf,
  sections16.3.2 and16.5.

The geometric character sum, positivity and trace/rank argument are
classical mechanisms. This is a repository-specific proposed reduction
for actual flat finite operators, without an original-priority claim.
The sources are background, not witnesses that the exact theorem here
was previously stated or that it has been independently assessed.
The unavailable lookup of the larger draft textbook was not treated as
evidence of novelty or expiration of any access.

Remaining single question: formally derive the per-site constant gradient
density of these actual normalized transverse physical characters, then
formalize the positive compressed-trace/rank inequality and compose it
with the existing tangent-kernel result. Do not postulate these as fields
of a structure. After three units without a derived lemma, useful theorem
or counterexample, retain failures and identify the exact blocker or
change route. Progress counter resets here for the explicit trace formula
and the negative actual-field example; formalization remains open.

No interacting/continuum Yang-Mills hypothesis is eliminated and no
physical mass gap is asserted. PR29 remains20/41,TermSource=0. Frozen
public AIRR v3 c9de923a...c3efb5b9 is unchanged and excludes this work.

## Unit048 partial formal bridge

PhysicalCharacterWeightDensity.lean at29eb3e6ce512f56a4f5e5699bf8b9ab9bc200cea
now derives exact actual character gradient density, weighted spatial-sum
energy, norm/divergence/Hodge identities. Two fresh Colab clones069/069b
matched; full evidence is in ../physical-character-weight-density-20261031/.
The normalized transverse strip basis and positive compressed-trace/rank
composition ABOVE remain paper-level. Do not inherit this partial bridge's
formal verdict for the whole rank-divergence conclusion.
## Unit049 normalized strip and energy sum

PhysicalTransverseCharacterStrip.lean at40bb2de8461a878c86d9cea4e80f7da31adb0e58
now constructs the actual normalized real orthonormal2R transverse family,
derives its divergence zero and span dimension, and proves the exact weighted
plus Hodge energy sum2(1+b_ij)*sum lambda_r. Fresh Colab clones071/071b
matched; evidence is in ../transverse-character-strip-20261031/. This closes
the normalized-family obligations mentioned as pending above. The positive
compressed-trace/rank and derivative-kernel composition still remain open;
do not inherit the strip's formal verdict for the whole rank obstruction.

## Unit050 penalty sharpness and refuted extension

`penalty-sharpness.md` gives a complete paper-level counterexample to dropping
the quadratic upper penalty hypothesis: C(x)=||x||^2 has zero derivative and
scalar output, but Phi(y)=c|y| recovers c||x||^2 exactly in every dimension.
Both maps can even be C1 using C(x)=||x||^(3/2), Phi(y)=c|y|^(4/3).
The note proves all zero-derivative and local-upper-bound-failure claims,
and distinguishes the valid C2-observation/C1-penalty tradeoff from a
weakening of the current theorem. No Lean verification or new publication
is claimed. The main positive compressed-trace/rank question remains active.

## Unit051 positive compressed trace/rank bridge

PositiveCompressedTrace.lean at e9fb5a4f6d9263c805a032d8e2be5078c484455c
now derives the generic positive trace lower bound on an actual submodule,
actual rank-nullity bound, actual inclusion-adjoint compression inner identity
and its positivity, and c*(dim S-dim F)<=trace(compression) under positivity
on S and kernel coercivity with c>=0. No ambient subspace invariance or
positivity after subtracting a kernel projection is assumed. Fresh own Linux
clones073/073b match; evidence is in ../positive-compressed-trace-20261031/.
This closes the generic trace bridge mentioned as pending above. The final
actual physical derivative-kernel/strip composition and quantitative tail
remain open; the full average-weight rank conclusion is not yet formal.
