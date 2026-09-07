# Candidate mixed image family for the actual rectangular carrier

STATIC DESIGN ONLY. No new compiler result, source equation verification,
physical inverse, uniform B0 or scalar-window attainment is claimed here.

## Current frontier after Addenda1203–1204

The all-reflecting image seam is now cold-sealed in1203. Periodic endpoint
transfer is separately HOT verified in1204; its exact production promotion
24dc691e4 is under a cold gate. Neither result supplies mixed coverage.

The next bounded draft tmp/NeumannPhysicalPeriodicSeriesDraft.lean reindexes
the one-branch periodic series by an integer translation equivalence. Its
identity of totalized tsums is explicitly NOT a summability certificate.
It is not added to the running gate, and compilation waits for the preceding
cold evidence to be preserved. This is the periodic seam substep of M4, not
the complete mixed-family M1/M2/M4 construction. Physical positivity/decay
windows must enter a separate convergence producer before operator action
is exchanged with this series. No duplicate reflection branch in FULL sides.

Historical frontier below records what was open before1203.

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
