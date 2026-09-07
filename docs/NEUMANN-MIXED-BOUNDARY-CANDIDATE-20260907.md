# Candidate mixed image family for the actual rectangular carrier

STATIC DESIGN ONLY. No new compiler result, source equation verification,
physical inverse, uniform B0 or scalar-window attainment is claimed here.

## Current frontier after Addenda1203–1208

The all-reflecting image seam is now cold-sealed in1203. Periodic endpoint
transfer is cold-sealed in1205 on24dc691e4. Neither result supplies mixed coverage.

The next bounded draft tmp/NeumannPhysicalPeriodicSeriesDraft.lean reindexes
the one-branch periodic series by an integer translation equivalence. Its
identity of totalized tsums is explicitly NOT a summability certificate.
It is not added to the running gate, and compilation waits for the preceding
cold evidence to be preserved. This is the periodic seam substep of M4, not
the complete mixed-family M1/M2/M4 construction. Physical positivity/decay
windows must enter a separate convergence producer before operator action
is exchanged with this series. No duplicate reflection branch in FULL sides.

Historical frontier below records what was open before1203.

### Located convergence route (static; 2026-09-07)

For fixed target x and source n, a positive coordinatewise period P gives
an injective map k -> x - (n + P*k) on Z^4. Compose the already sealed
summable_cmp89SignedLatticeL1ExponentialWeight with this injection, multiply
by the existing certificate amplitude, and apply Summable.of_norm_bounded
using neumannActualFullGreenDecayCertificate.bound. This uses the literal
(2.46) kernel and retains every amplitude/radius/pair/mass window.

This route needs only P_mu != 0 for injection; the physical period is
P_mu=L^j*blockCount_mu with positive blockCount. Zero periods must not be
admitted into a convergence theorem: repeated indices then need not decay.
The all-coordinate translation identity permits zero periods algebraically;
its more general signature is not itself a convergence producer.

This injection argument proves convergence only. Bounding it by the total
fine-lattice mass would pay the fine rate rho/L^j and is NOT a uniform B0
producer; do not use that coarse upper bound as attainment of window15.
The sharper residue bound and the fine/block metric conversion remain
necessary for quantitative regional estimates. For mixed branches the same
argument requires injection separately within each fixed allowed branch;
FULL directions must still have only their single branch.

The convergence route is now HOT compiled (Addendum1208), not cold-sealed, in
tmp/NeumannPhysicalPeriodicSummabilityDraft.lean: injection, generic decay
composition and literal mass-uniform physical specialization. The period
may be any nonzero integer for convergence; ONLY the separate covariance
law requires block alignment. These different hypotheses are intentional.
The source windows remain verbatim. No quantitative total-mass bound is
installed by the draft. PRE-VALIDATION retained until exact promotion/cold gate.
The periodic series draft also passed HOT: two series declarations and three
convergence declarations, with the exact allowed trios. Archive7bf052a0e1117bb525e4633dc0fe07eee918ed1a660f208b22c2ef313e33209e
independently verified together with its cold parent. V1/v2 instrument failures
remain in1206/1207, not erased. Next: promote these exact proofs and audit,
then one cold focal gate; mixed M1/M2 and full point-source action remain open.

Exact production promotion is now written as NeumannPhysicalPeriodicSeries,
NeumannPhysicalPeriodicSummability and their shared SeriesAudit. Only the
module header and placement of #print axioms differ from HOT drafts; body
equality checked textually. These leaf modules remain PRE-VALIDATION and are
not silently installed in YangMillsCore. Cold queue must build both modules
and audit the five exact names. The cold runner is the next preparation step;
no second runtime is opened before its source/hash contract is ready.

The historical paragraphs below record the earlier design audit. M3 is no
longer wholly open: the literal full Green common block translation and
simultaneous half-cell reflection are cold-sealed in Addendum1197. Their
exact entry points are neumannActualNormalizedFineGreen_commonBlockShift
and neumannPhysicalGreen_blockBoundaryReflection_massUniform. The latter
retains all source mass/strip windows; the former is the integral identity
with arbitrary mass/a and no added positivity condition. Neither is an
arbitrary fine-translation theorem.

Addendum1202 preserves the HOT all-reflecting physical seam and both ghost
values, with the explicit fine/block boundary equality. Its production graph
at0f43fbdc5 is currently under a separate cold gate. This does not implement
the mixed family, its coverage, or the periodic seam.

For a FULL coordinate with fine period P=L^j*N, the remaining periodic seam
can use common block shift N in that coordinate. Pointwise transfer is
G(x+P,y)=G(x,y-P); at source image n+k*P, the source index becomes k-1,
without a parity flip. The branch subtype must remain unchanged in that
FULL coordinate. This algebraic route is a design obligation, not a theorem
already obtained from the all-reflecting seam. The factor L^j is required:
replacing P by a non-block-aligned fine period is not licensed by M3.

M1/M2 and mixed M4 remain open. In particular, use exactly one branch in
FULL coordinates and preserve the non-strict carrier fit. The full-lattice
physical point-source equation remains an independent prerequisite.
The live directional-mask cold gate and its prepared HOT composition are
unchanged. This note refines the already open full/proper-side design gate;
it is not permission to replace the existing source kernel silently.

## What the inspected tree fixes

NeumannRectangleDirectionalMasks keeps the original hypotheses 0<m_mu<=N.
Its production cold gate is sealed in ledger1180; the literal masked action
has a separately preserved HOT PASS in ledger1181, not a cold seal. The separately cold-sealed
NeumannRectangleWrapProbe and NeumannFlatInternalBondAction establish that
site fit alone does not erase actual torus wrap bonds.

The literal full-image family in NeumannIntegerImageCountingKernel uses
2*k*m+n and 2*k*m-n-1 in EVERY coordinate. Its scope is the existing CMP89
reflection construction. NeumannActualFullGreenReflectionSummability fixes
the target and varies source images of the full (2.46) kernel. Neither
result already identifies that family with a mixed torus/Neumann inverse.

## Candidate retaining all original carrier inputs

Let B>0 be the fine block side; fine ambient period P=B*N and fine side
h_mu=B*m_mu. In direction mu classify FULL by m_mu=N, otherwise PROPER.
For an integer source coordinate n in [0,h_mu), use:

- FULL: n + k*P, with a single branch.
- PROPER: n + 2*k*h_mu or -n-1 + 2*k*h_mu.

Use a proof-carrying branch type that forces the reflection bit to false
in FULL directions. Summing over both bits there would duplicate the
periodic images, and would change the delta normalization. This is not
absorbed into a constant. The candidate has at most 2^4=16 branches,
independent of B, K, N and the side lengths; that count still needs a theorem
if the candidate is implemented.

All proper directions recover the existing printed half-cell image family.
All full directions instead give a periodic image family. A mixed rectangle
uses the two prescriptions direction by direction; it does not cut any
actual wrap bond or shrink a region to make strict fit true.

## Finite proof obligations before adoption

### M1/M2 implementation boundary inspected during the periodic cold gate

Static reading of NeumannImageIntervalCoverage and
NeumannImageRectangleCoverage confirms that their coverage varies the
original point as well as translation and branch. For a FIXED source the
required consequence is injectivity, not surjectivity onto the lattice.
Keep these two signatures separate in the mixed replacement.

The missing FULL-coordinate primitive has exact map
`(k,n) -> n + P*k`, with `n : neumannImageIntervalPoint P` and `0<P`.
Its proposed inverse is `(u/P, u%P)` using Euclidean integer division,
including negative u. There is no Bool in this coordinate. The PROPER
primitive can reuse `neumannImageIntervalFamily_bijective` verbatim at
side h. Coordinatewise assembly should first use a dependent index whose
FULL branch is a singleton, and only then prove equivalence with the
global proof-carrying Bool-vector presentation. Do not supply both Bool
values and subsequently divide the sum by two.

This yields a finite next proof queue: FULL quotient/remainder bijection;
mixed coordinatewise equivalence and literal-image formula; fixed-source
injectivity; branch-count bound; owner intertwiner. The branch bound is
at most `2^d` (16 in dimension four), independent of all side lengths.
No item in this paragraph is newly compiler-verified.

The independent first-coordinate draft is now written at
`tmp/NeumannPeriodicIntervalCoverageDraft.lean`: quotient, remainder,
injectivity, surjectivity, bijectivity and the FULL owner identity, with
six explicit audit names. It imports the cold-sealed interval coverage,
not the currently pending physical series. Overlay textual guard passed
in 0.095257s (15,376,384 bytes observed peak RSS); import-prefix guard
passed in 0.0832739s (15,097,856 bytes). These are textual checks only;
no Lean was run locally and the live cold queue was not altered.

For M2 the FULL owner identity is exactly
`(n + B*(k*N))/B = n/B + k*N`, with `0<B`.
The inspected existing proof `neumannIntegerTranslatedOwner` already uses
`Int.add_mul_ediv_left` for the analogous PROPER shift. Reuse that integer
division mechanism and the existing reflected-owner theorem; do not add
a new counting coefficient or confuse ambient period B*N with owner
divisor B. The coefficient in `neumannIntegerCountingIndicator_image`
stays unchanged, and its generated-operator identification remains a
separate physical obligation.

First determine whether the actual physical carrier producer guarantees
proper sides. If it does, prove that fact from its geometry and use the
existing all-reflecting route on that justified domain. M1-M4 below are
conditional obligations for adopting a mixed-family route, not four new
mandatory bricks added regardless of the physical consumer. The arbitrary
rectangular finite-action theorem itself must still retain its full inputs.

M1. Construct the exact full-family integer coverage/bijection, including
the single periodic branch in full directions. Reuse the existing proper
interval coverage; add ordinary Euclidean quotient/remainder in the full
case. Count each point once, not only show coverage.

M2. Prove the block-owner intertwiner at the same image index. For a full
direction the required identity is (n+k*B*N)/B = n/B+k*N; proper directions
use neumannIntegerTranslatedOwner and neumannIntegerReflectedOwner. Keep
the physical counting coefficient and the single block-volume cancellation
from the sealed generated-average dictionary unchanged.

M3. Derive covariance of the ACTUAL full two-endpoint (2.46) Green under
the required common block translations and coordinate half-cell reflections.
Source-image summability or a source-image permutation alone does not prove
target-boundary invariance. The located depth-one negated-endpoint swap
theorem is not this arbitrary-depth covariance law.

M4. Apply the actual masked Laplacian and generated averaging action to the
constructed image series. Prove the periodic seams in FULL directions and
the half-cell Neumann seams in PROPER directions separately; interchange
only with explicit summability. The full-lattice normalized point-source
equation and fine-density-to-counting factor B^-4 must be supplied once.
Only then may inverse uniqueness identify the regional Green.

This candidate could preserve the original non-strict carrier domain, but
it remains unimplemented and unverified. It does NOT discharge M3/M4 or
the independent full-lattice Fourier/operator equation by defining a new
kernel. Any adoption must update the physical endpoint explicitly rather
than relabel the all-reflecting CMP89 (2.42) formula as mixed-periodic.

Counters unchanged: 20/41, TermSource=0, window15 not attained.

## Primary-page check, 2026-09-07

Read the complete existing renders of printed pages572,582,583,584 directly,
not merely their OCR or an external report. The PDF matches the previously
catalogued primary digest416e2b1f00b52e7235ab27d2be066b50d42dde33cf8596baeae0a6688b145143.

Page572 explicitly allows subsets of a periodic torus as another ambient
setting, fixes half-open blocks in(1.1), and defines(1.3) by summing bonds
whose two endpoints are in Omega. This agrees with retaining actual wrap
bonds when both endpoints are active; it does not justify cutting them.
Lemma2.4 on page582 describes arbitrary block-built rectangular subsets of
the lattice. Its proof on page584 invokes the reflection formula(2.42) and
then the full-lattice Fourier equation(2.44). These inspected pages do not
provide a finite-torus strict-fit hypothesis or its physical producer.
This is a scoped source reading, not an assertion about every page or every
downstream CMP95/CMP96/CMP99 domain construction.

The apparent inclusive endpoint on page584 is already handled explicitly
by BalabanCMP89NeumannReflectionScaleDictionary: distinguish its geometric
envelope from the half-open block sites of(1.1). The present reading confirms
both printed conventions; it does not announce a new endpoint no-go or
change the established integer image family.

Private render provenance (not committed as public paper copies):

- tmp/pdfs/cmp89-massdef-02.png, printed572:
  39af128b7107dbe230be49c87168e984c8c0df0493b97fe309fc6996e4297ae3.
- tmp/cmp89-p-12.png, printed582:
  d0961a39a1d0cc1121656b35c63ac3c7954e2edf21b18f421435a6342bfd4a14.
- tmp/cmp89-p-13.png, printed583:
  6d0ac2a169d83f0e5015d5433ed490eb5b5810879d8daaf63cb9ea3a9214369f.
- tmp/cmp89-p-14.png, printed584:
  36ec3a0c2c0d3f9e1e8acdd785d2c11195c89a134657756a401b2bd0d1827f5d.

Hash-only local check: exit0,0.0949014s,15880192 observed peak RSS.
No new render, compiler job or mathematical seal was required for this check.

## Scoped consumer audit after ledger1181

The existing canonical rectangular reflection gate takes hm>0 and hfit<=N,
not strict fit. Its withdrawn physical specialization must NOT be used to
smuggle a proper-side hypothesis into the actual (2.46) replacement.
SourceSeparatedGeneratedPhysicalLargeBlockCutoff takes arbitrary Omega at
ambient side2*(K*Q); it is not itself a rectangle/proper-fit producer.
The inspected uniform-owner certificate also retains non-strict hfit and
an explicit representation input. These signatures do not establish a
strict-fit lemma for the eventual regional carrier. This is a scoped audit,
not a claim that no such geometric theorem can exist elsewhere.

The next shared algebraic primitive for M3 (needed for proper reflections
even if FULL directions disappear) is finite-average half-cell phase, not
the real-slice conjugation theorem. A Mathlib-only PRE repro is now written
at tmp/NeumannHalfCellPhaseRepro.lean: reverse the finite exponential sum
using Finset.sum_range_reflect. It allows every complex c, including c=0
and exp(c)=1; a quotient geometric-sum proof excluding those cases would
lose the central modes. No compiler result is claimed. After this primitive
passes, specialize to the ACTUAL entire average factor with c=i*z/N; its
phase must travel into the two-endpoint kernel before asserting covariance.
