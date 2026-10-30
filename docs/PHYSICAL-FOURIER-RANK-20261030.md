# A constructed physical Fourier image and its coarse rank obstruction

The real physical subspace is now constructed as the range of the actual
real-linear map from the complex centered Fourier band, viewed over the reals,
through E_j. The map uses the previously proved addition/scalar identities;
its injectivity follows from the previously proved injectivity of E_j on
all complex profiles. No basis, image dimension or comparison subspace is
supplied as an assumption.

For n>0,Nc>=2,j:Fin d and2R<n, the proved dimension is

    dim_R S = 2*(2R+1)^d.

The factor2 counts real and imaginary values stored in two distinct internal
coordinates. It is not a claim about twice as many independent real-valued
scalar Fourier functions, nor a q-fold vector-field band. The domain is the
existing complex span equipped with its ordinary real scalar action, not a
new assumed realification. Every member of the range has a proved finite
coefficient representation; hence the verified energy bound applies to every
member of this actual subspace, not only to its named generators.

The concrete finite flat obstruction has the following proved statement.
Let K0 be the repository's actual flat Hodge operator on its Euclidean-coordinate
cochains, C:E->F any real linear measurement into a finite-dimensional real
space, V:E->E any real linear repair, and Phi:F->R any function with Phi(0)=0.
No continuity, sign, symmetry or quadratic form is required of Phi; no symmetry,
positivity or norm estimate is required of V. Set b=4*pi^2*d*R^2/n^2. If c>b
and a full-space estimate

    c*||A||^2 <= <A,K0 A> + Phi(C A) + <A,V A>

holds for every A, then necessarily

    2*(2R+1)^d <= dim_R F + rank_R V.

This budget is necessary only. Meeting it does not prove a repaired estimate;
cross-coupling can still obstruct it, as the earlier dossier counterexample
shows. If the budget on the right is smaller, that full-space estimate is false.
Rank-nullity supplies an actual nonzero vector in S annihilated by both C
and V, so both repairs vanish there and the already proved low-energy bound
contradicts c>b. In particular C is arbitrary; it need not factor through
the original coarse Q, preserve an old witness, or be any specific block map.
The bound uses the dimension of F (a conservative measurement budget), not a
claim of the sharper rank(C) bound, which would need a separate formulation.

For a concrete illustration, take d=4,Nc=2,n=16,R=1 and any chosen bond
direction. The real band dimension is2*3^4=162 and b=pi^2/16<1. Thus12real
measurement coordinates plus a fine repair of rank at most149 cannot produce
the full-space bound with c=1, regardless of the nonlinear penalty with
Phi(0)=0. This is an elementary instantiation of the general statement, not
a separate named oracle theorem or a claim about the program's chosen target
constant. Scaling the operator physically changes b and must be re-audited.

The theorem's exact verification status is recorded below. This is a finite,
flat, unit-spacing statement in the existing abstract Lie-coordinate model.
It is not a nontrivial-background theorem, a matrix Lie algebra identification,
a continuum limit or a positive Yang--Mills mass-gap theorem. No asymptotic
choice of R,n,L, prescribed coarse dimension or q-fold formula is silently
inserted. The distinction from physical scaling eta=1/L remains essential.

## Verification

Sourcea79e6e4b2e5de72e73bd6109069eb2f82127c355 passed the complete focal
build and six named oracle reports in two fresh serial Colab clones. Each
full package was recovered and validated for12manifest entries,2source files,
9exit-zero steps and6reports using exactly propext,Classical.choice,Quot.sound.
Both runs' oracle validator accepts the true log and rejects3actual-field
mutations in both normal and optimized(-O) Python. No acceptance uses assert.

| Artifact | SHA256 of raw bytes |
| --- | --- |
| run031.zip | d6728e70766dd71be8d859d74bf7f86d52ba972ba58b05e01efa69f16d2e1a90 |
| run031b.zip | cf9632641a8ba0ae7d914bfefbf4094f337ff8f53baaafdc7767fe932ada34ca |
| target .olean, both | db3fac30520d43f27afc99fab94edf8c2089e41e33a500fd0274316ed39874c2 |
| oracle.log, both | 4afbf5f9e27c790f309475918191d55af0978bc24b350d5757d8a7388ad0cad2 |
| source-hashes.json, both | 9c8ffde577a769c2b980fc45b0674e2a1a037c4e0819089a0f9c4df2f96ecacf |

Normalized LF source SHA256:
module7f26246c244d5be04b393d581bda090a9aa6d219303a3094c091b0aba59f4e02;
oracleaad585e4364e478ac3a8023fef77a3c87a625c832206d83c33146281b0181b09.
Only source LF hashes are normalized; compiled outputs/logs/ZIPs are raw.
Source SHA, .olean, oracle.log and source-manifest digests are identical in
the two fresh runs. The six verified declarations are
centeredPhysicalBandMap_injective,physicalCenteredFourierBand_finrank,
physicalCenteredFourierBand_representation,physicalCenteredFourierBand_hodge_le,
physicalCenteredFourierBand_coercivity_budget,physicalCenteredFourierBand_coercivity_false.

Run031:01:51:16.561614-01:56:17.096080UTC30October2026,300.534466s;
run031b:01:57:20.203140-02:01:22.867483UTC,242.664343s. Both automatically
released and disconnected controls observed. Failed run030 at1ce5b87 lasted
01:42:33.060286-01:47:38.508656UTC,305.448370s; its rawZIP SHA256 is
b9ebf391d7e84b41b1df13a8be5f86df1eaddc5ab4d95387a7406c9c551babe3.
All three were this chat's own serial CPU/high-RAM runtimes. Total execution
intervals including failure:848.647179s; additional allocation/release overhead
and compute units unmeasured. No GPU, shared runtime, local Windows Lean/Lake
or new purchase. The first complete passing ZIP was recovered and validated
before the second fresh clone started. Scoped elaboration allowances of800000
and1200000heartbeats affect resources only, not statements, axioms or kernel checks.

Complete ZIPs, validations, normal/-O selftests, exact executed notebook,
failed input and runtime record are preserved under
`reproducibility/physical-fourier-rank-20261030/`. The convenience Python copy
trims only excess EOF blank lines; the notebook preserves exact executed input.
This is focal module closure, not an independent scientific review or terminal
whole-repository audit. No new paper/deposit is created by this code unit.

The first candidate1ce5b87 failed in run030 because the finite-span lemma
requires an explicit scalar parameter before applying `.mp`. The correction
supplies the existing complex scalar type; no mathematical statement,
hypothesis, oracle name or acceptance rule changes. The full failed ZIP and
its exact notebook/input hashes are retained and never counted as a pass.

## Originality, relevance and sources

This is a concrete formal instantiation of classical finite-dimensional
rank-nullity/min-max reasoning. The finite band dimension, counting norm and
operator energy have all been constructed in this repository rather than
postulated by an interface. That is the reduction established here; it does
not establish priority for a new general theorem and does not justify a
separate paper of a small corollary. It belongs in the existing dossier.
The primary source for the exact APIs used is Mathlib at the pinned revision:
[finite-dimensional injective maps](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean)
and [finite span coefficient representations](https://github.com/leanprover-community/mathlib4/blob/07642720480157414db592fa85b626dafb71355b/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean).
The actual physical energy theorem and abstract kernel-intersection proof
are the versioned repository dependencies at the tested SHA. Dodziuk1976,
cited in the existing Hodge note, supports historical combinatorial-Hodge
background only, not the priority or exact normalization of this code result.
Formal validity, originality and scientific relevance remain distinct.

## Model assessments and review context

Construction and orchestration are by this chat's Codex assistant; its exact
backend model identifier is not exposed here. Colab reproductions by the same
workflow are mechanical Lean checks, not independent scientific reviews,
model scores, peer review, acceptance or publication. No earlier PDF score is
inherited. No new AIRR/ai.viXra deposit or PDF is generated by this code unit.
PR29 remains20/41,TermSource=0; no physical hRpoly producer is claimed.

## Next scoped question

The next bounded question is whether this fully constructed finite budget
rules out a uniform positive unit-spacing threshold for arbitrary fixed-
dimensional measurements and uniformly bounded-rank repairs under refinement.
Choose R to exceed the fixed budget, then refine until b<c. A finite harmonic
quotient or a rescaling of the same measurement alone would not evade that
argument. The actual hRpoly normalization must be audited alongside this:
a physically scaled K0 changes the premise and remains outside the claim.
The refinement-family quantifiers are a next step, not a theorem proved here.
This finite theorem alone must not be upgraded to the prior q-fold asymptotic
constant or to a refutation of a differently normalized physical model.
Consolidate the closed statements and their complete reproduction records
into the existing paper dossier, without duplicating deposits or inheriting
reviews. Falsifiers include a wrong real dimension, an image/type mismatch,
a misplaced scaling factor, or confusing the divergence gaugeConstraintQCLM
with the arbitrary coarse measurement C. After three units without substantive
progress, preserve the precise block and change route.
