# Step 8b.24 / C6c.1c — source-faithful fine-lattice Holder route

Status: static design only.  Nothing in this note has been checked by Lean,
Lake or an axiom audit.  It must not be promoted before the Step-8b.23 and
Step-8b.24 C6b prerequisites, nor before the D1--D4 left-derivative queue, have
their own cold seals.

## Scope and source target

CMP89 Eq. (2.49), visually fixed on printed page 585, is the normalized
Holder difference

```text
|x-x'|^(-alpha)
  * ((partial_mu^xi (G_j Q_j^*))(x,y)
      - (partial_mu^xi (G_j Q_j^*))(x',y)).
```

Its Fourier numerator is

```text
(exp(i*(p'+l).(x-x')) - 1) / |x-x'|^alpha,
```

the remaining endpoint phase is based at `x'-y`, and the derivative symbol is
`partial_mu^xi(p'+l)`.  The physical sites lie in `xi * Z^4`, with
`xi = L^(-j)`.  Therefore an integer displacement `u` denotes the physical
displacement `xi*u`; no unit-lattice alias cancellation may drop that factor.

Direct visual inspection of CMP96 printed page 234, Proposition 2.2 / Eq.
(2.67), fixes the consumer range as

```text
0 < alpha < 1.
```

Both inequalities are portante.  The strict upper inequality is the
source-facing summability gate: the alias exponent `1 + (1-alpha)/4` must be
strictly greater than one.  The already sealed Euclidean phase lemma permits
`0 <= alpha <= 1`, but neither endpoint belongs to the literal CMP96 consumer
range and neither may be admitted by this producer merely because the
primitive phase estimate still types there.

The same render fixes the six-component scale vector of (2.67).  In order, the
value, left derivative, right adjoint derivative, two local Holder actions and
Laplacian carry

```text
[(L^j * eta)^2,
 L^j * eta,
 L^j * eta,
 (L^j * eta)^(1-alpha) * (holderSeminorm zeta alpha + abs zeta),
 (L^j * eta)^(1-alpha) * (holderSeminorm zeta alpha + abs zeta),
 1]
```

times the common localization factor

```text
O(1) * exp (-(1/2) * delta0 * d(y,y')) * |lambda|.
```

Here `holderSeminorm zeta alpha` and `abs zeta` are source notation, not Lean
names proposed by this note.  Their exact existing repository representations
must be identified before a public signature is written.  In particular, the
factor `(L^j*eta)^(1-alpha)` and the loss from `delta0` to `delta0/2` must not
be absorbed into an unnamed constant.

### Measured repository interface gap

A case-insensitive declaration search over `YangMills/RG/*.lean` finds the
sealed Fourier Holder quotient and unit-edge normalization, but no finite-field
local Holder seminorm and no predicate representing the cutoff-localized norms
used in CMP95 (1.109)/(1.111) and CMP96 (2.67).  This is a genuine interface
gap: the future producer must construct the seminorm, not accept its value or a
ready-made Holder action bound from the caller.

The tree does already contain the seam-safe coordinate primitive needed for a
torus definition:

```text
cmp116CMP89PeriodicCoordinateDisplacement target source
```

and proves that its `natAbs` is the literal coordinate torus distance.  A
candidate source-faithful finite seminorm therefore ranges over distinct target
sites whose *physical* Euclidean separation is at most one and takes the finite
maximum of

```text
norm (F x - F x') / physicalEuclideanDistance(x,x')^alpha.
```

For the localized clauses it is applied to `x |-> zeta x * F x`; the right-hand
side separately retains the corresponding cutoff seminorm and cutoff sup norm.
This is only a design constraint, not yet a definition: the OCR of CMP95
(1.109) has the expected `0 < |x-x'| <= 1` pair restriction, but the exact page
35 formula still requires a primary visual render before the metric and carrier
are frozen in Lean.

The measured artifact is `tmp/cmp95-part1-layout.txt`, around lines 880--898.
It is a full-page text extraction of printed page 35 and identifies (1.109) as
the two Holder norms, but corrupts precisely the pair restriction, denominator
and exponent.  The cataloged private render `cmp95/render/cmp95-page-19.png`
and primary PDF `cmp95/1103941451.pdf` are not mounted in this checkout and
`YM_SOURCE_ROOT` is unset.  The official DOI `10.1007/BF01215753` and an
in-app-browser check both expose only Springer subscription preview.  This OCR
is therefore locator evidence, not formula evidence, and must not be promoted
to `visual_confirmed`.

The local acquisition boundary was rechecked on 2026-08-17.  The exact
artifacts that bracket the missing primary page are:

```text
tmp/cmp95-part1-layout.txt
  SHA256 C05472DCFCF7957D19CC49101754798055339B07EBDEBB1E75E7B8162B73E08A
  OCR locator for printed page 35; (1.109) is at lines 880--898.
tmp/pdfs/cmp95-page-20.png
  SHA256 40E9EB1F93E13650BB8B585488C9BF2B62716F858CE5F4E3F201BB8C8BEF7658
  visual render of printed page 36, beginning with (1.112).
tmp/pdfs/cmp95/page-21.png
  SHA256 F41FC21E20A93C8886BCF9C9515E1BED3C9F1721E87D6AE3AE36FFEA9FAAE708
  next rendered page; later proof material, not (1.109).
```

There is no local `cmp95-page-19.png` or `1103941451.pdf`.  The official
Springer endpoint for DOI `10.1007/BF01215753` identifies the correct article
but exposes only subscription preview.  Therefore the acquisition gate is one
specific object: a primary render of printed page 35 (PDF page 19 in the
cataloged copy).  Until that object is present, the OCR may locate (1.109) and
the adjacent renders may bracket it, but neither may certify its symbols.

A direct visual check of the locally rendered CMP99 printed page 397 gives an
independent source-side cross-check: Eq. (3.40) defines the covariant Holder
norm with the literal restriction `|x - x'| <= 1`, transports along a shortest
contour `Gamma_(x,x')`, and states that the `eta` scale is used unless a
different scale is marked explicitly.  The paragraph immediately above says
that these norms are identical to CMP95 (1.108)/(1.109), modulo replacement by
covariant derivatives.  This confirms that H2b must obtain a local-pair witness
from its concrete seminorm carrier.  It remains secondary cross-check evidence:
the exact CMP95 metric, zero-distance exclusion, denominator and exponent are
not frozen until the primary CMP95 page is visually available.

This branch is an internal input to the CMP96 multi-action construction.  It
is not one of the four fields of
`CMP99Eq342SourceLocalizedGreenCertificate`, whose literal fields are value,
left derivative, right adjoint derivative and Laplacian.  Consequently a green
Holder prefix does not move `20/41`, attain window 15 or inhabit `TermSource`.

## Measured acceptance boundary

The old unit-lattice Holder chain is valid algebra on integer displacements
but is not a physical producer at fine spacing.  The sealed phase-scale no-go
forbids reusing its alias cancellation at displacement `xi*u`.  A physical
producer must retain each noncentral alias phase until the norm is taken and
must transport the phase, derivative symbol, averaging factors and endpoint
normalization at the same fine scale.

The Holder branch also cannot be obtained by taking the difference of two
final left-derivative bounds.  That loses the numerator cancellation before
division by `|x-x'|^alpha` and does not reproduce Eq. (2.49).

## Restartable bricks

### H1 — physical fine-lattice Holder phase quotient

Construct the literal physical displacement

```text
r = cmp89Eq249FineLatticeSpacing L j * (x - x')
```

and prove the Euclidean quotient estimate for the complete alias momentum,
without replacing `r` by the integer difference and without a sup-norm or
hidden dimension factor.  The conclusion must retain `alpha`, `xi` and every
alias phase explicitly.  The already sealed constant `2` may be reused only
after the equality of its abstract displacement with this physical `r` is
proved.

A static H1 draft now exists in
`tmp/BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient.draft.lean` with three
declarations.  It derives denominator positivity internally from `xi > 0` and
`u != 0`, then specializes the already sealed phase quotient to the literal
momentum `p + 2*pi*m`.  It deliberately does not define the local seminorm or
freeze the CMP95 (1.109) carrier.  The draft and its audit are unelaborated;
their names carry `_draft` until promotion, while the audit records the
intended public names after promotion.

### H2 — mass-uniform complete Holder-integrand strip majorant

Assemble and bound the exact complete Eq.-(2.49) integrand at general
`alpha`:

- central branch treated separately;
- every noncentral phase retained inside its alias summand;
- the Holder cancellation
  `exp(i*q dot (x-x')) - 1` remains inside the same summand as the transport
  phase `exp(i*q dot (x'-y))` throughout the strip estimate;
- one scaled derivative symbol;
- the entire averaging amplitude;
- the complete stabilized denominator and mass-uniform reciprocal;
- source redistribution exponent `1 + (1-alpha)/4`.

Use `0 < alpha < 1` to discharge strict summability.  Preserve the visible
constants `2` and `3^(1-alpha)`.  No alias-cardinality factor, positive-mass
premise or caller-supplied endpoint estimate is admissible.

The measured reuse boundary is now exact:

- `BalabanCMP89Eq249StabilizedComplexIntegrand` already defines the literal
  complex bare alias numerator at arbitrary `alpha`;
- `BalabanCMP89Eq251FineLatticePhasedNoncentralSum` already keeps the physical
  phase inside every alias and sums without cardinality loss, but only at the
  specialization `alpha = 0`;
- `BalabanCMP89Eq251ComplexNoncentralEndpointQuotientBound` proves the strip
  radial cancellation and source-weight redistribution only at `alpha = 0`;
- `BalabanCMP89Eq251NoncentralRealIntegrandBound` has the correct general
  exponent `1 + (1-alpha)/4`, but only on the real slice.

Thus H2 is not a wrapper around the sealed left-derivative endpoint bound.  Its
new analytic core is the complex-strip analogue of the general-alpha real
quotient: retain the physical Holder numerator in the complete integrand,
obtain the radial power `norm(q)^(alpha-1)`, redistribute it to exponent
`1 + (1-alpha)/4`, and only then perform the alias sum.  Reusing the
`alpha = 0` complex constant with `alpha` merely threaded through the type, or
bounding the two endpoint terms separately before division by
`|x-x'|^alpha`, would be a false producer.

H2 must be split into four finite subbricks rather than presented as one
opaque estimate:

```text
H2a  complex-strip Holder phase quotient at general alpha
H2b  noncentral complete-quotient bound at general alpha
H2c  general-alpha alias summation with exponent 1+(1-alpha)/4
H2d  central/noncentral recombination into the stabilized full integrand
```

Static inspection of the literal stabilized numerator further splits H2d at
its only honest boundary:

```text
H2d1  retain the physical Holder quotient and transport phase inside every
      noncentral alias; on the signed transport contour, sum to one exact
      decay factor times the H2c general-alpha constant;
H2d2  bound the zero-alias Holder branch with the same physical quotient;
H2d3  combine H2d1/H2d2 with the central fine-symbol bound and only then
      multiply by the common stabilized reciprocal.
```

H2d1 is now written statically in
`tmp/BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSum.draft.lean`.
It is intentionally not the old endpoint factorization: at fine spacing the
reciprocal-alias phases are not equal.  Instead the literal phases stay inside
the finite sum, while their norms on the signed contour share one exact decay
because the alias shifts are real.  The draft has not been elaborated and does
not prove contour equality.

H2d2 is now written statically in
`tmp/BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranch.draft.lean`.
It proves the dimension-four Brillouin bound `||p||_2 <= 2*pi`, identifies the
literal zero-alias numerator with the physical fine Holder central branch, and
retains the same exact signed transport decay.  It deliberately stops before
the central/noncentral recombination and common stabilized reciprocal.

H2d3 is now written statically in
`tmp/BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBound.draft.lean`.
It first proves the literal numerator split
`central + centralFine * noncentral`, then applies the single mass-uniform
stabilized reciprocal.  Its output is still only a pointwise bound on the
signed contour: contour equality and the source/owner metric dictionary remain
outside the theorem.

The elementary decomposition to be used in H2a is also fixed.  For
`z = q + I*b` and physical displacement `u`, keep

```text
exp(I*z.u) - 1
  = exp(-b.u) * (exp(I*q.u) - 1) + (exp(-b.u) - 1).
```

In dimension four the existing theorems
`sum_abs_le_two_mul_cmp89Eq251EuclideanNorm_fin_four` and
`norm_exp_I_cmp89Eq251EntireAliasPhase_le_growth` give
`|b.u| <= 2*rho*||u||_2` on the full coordinate strip.  Hence the first term
retains the real Holder cancellation, while the second is the vertical-strip
correction and carries a visible factor of the form
`rho * exp(2*rho*||u||_2) * ||u||_2^(1-alpha)`.  This correction may be made
uniform by `||u||_2 <= 1` only if that local-pair restriction is confirmed in
the primary render of CMP95 (1.109).  CMP99 Eq. (3.40), visually checked on
printed page 397, independently confirms the literal `|x-x'| <= 1` carrier for
the covariant version and explicitly points back to CMP95 (1.109), but it does
not replace the missing primary render.  CMP89 Lemma 2.4 / Eq. (2.36), visually
checked on printed page 582, states its Holder estimate for arbitrary points
in the domain and does not itself supply this restriction.  Therefore H2b's
local specialization and its final constant remain deliberately unfrozen until
the CMP95 page is rendered.  No proof may silently import `||u|| <= 1` from
the OCR or absorb the vertical correction into the `alpha = 0` constant.

The precise global H2a target, which does **not** need that restriction, is
the following source-shaped inequality for `0 <= alpha <= 1`, `u != 0`, real
`q`, and coordinate strip `|b_mu| <= rho`:

```text
||exp(I*(q+I*b).u)-1|| / ||u||_2^alpha
  <= 2 * exp(2*rho*||u||_2)
       * (||q||_2^alpha + rho*||u||_2^(1-alpha)).
```

Its two reusable inputs are already in the tree.  The real phase quotient is
`norm_cmp89Eq251_phaseFactor_div_displacement_rpow_le`; the vertical change
is an instance of `norm_complex_exp_sub_exp_le_of_norm_sub_le` with the real
phase as `B`, followed by the four-dimensional `l1 <= 2*l2` theorem.  Thus the
future CMP95 visual check does not gate H2a itself.  It gates only the H2b
specialization replacing `||u||_2^(1-alpha)` by one on the local pair carrier.
That specialization must derive membership in the carrier from the concrete
seminorm index, never receive `||u|| <= 1` as an independent hypothesis.

A four-declaration static H2a draft now exists in
`tmp/BalabanCMP89Eq249ComplexStripHolderPhaseQuotient.draft.lean`.  It proves
the exact real/imaginary phase split, the four-dimensional strip budget
`2*rho*||u||_2`, the exponential variation from the common phase, and the
global quotient above with the residual `||u||_2^(1-alpha)` visible.  Its audit
names the intended public declarations.  Both files are unelaborated and
remain PRE-VALIDATION; their textual guards are not compiler evidence.

The H2b radial bookkeeping is now fixed in
`tmp/STEP8B24-C6C1-H2B-SPLIT.md`.  Multiplying H2a by the sealed
derivative/average/fine-symbol quotient produces a source branch
`||q_m||^(alpha-1)` and a vertical correction `rho*||q_m||^(-1)`.
They redistribute at `alpha` and `0`, respectively.  A separate four-lemma
static draft proves exponent antitonicity and the pointwise domination of the
`alpha = 0` product weight by the single general-`alpha` weight.  This keeps
the combined constant literal as
`2*exp(2*rho)*R(rho)*(3^(1-alpha)+3*rho)` and prevents a hidden second series
or alias-cardinality factor.  The actual source-generic H2b producer still
waits for the primary CMP95 carrier and for compiler validation of H2a and the
monotonicity support; no complete-quotient theorem is claimed yet.  The
physical hRpoly specialization is less blocked: its sealed bond dictionary
gives a unit integer displacement, H1 now has static exact normalization
`||xi*u||_2 = xi`, and the existing inverse-scale theorem gives `xi <= 1`.
That route must construct the local-pair witness internally and must not wait
on, or pretend to prove, the general CMP95 seminorm interface.

That physical specialization is now written as the two-declaration static
subbrick
`tmp/BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient.draft.lean`.
It constructs `u != 0`, rewrites `||xi*u||_2` exactly to `xi`, and discharges
the H2a residual power by `xi^(1-alpha) <= 1`.  It stops before multiplying by
the complete endpoint quotient.  Its imports are an explicit future contract
on the promoted H1 and H2a leaf modules, so the subbrick remains unelaborated
and PRE-VALIDATION and is not yet a build target.

The following radial-only H2b support is also written statically in
`tmp/BalabanCMP89Eq249ComplexHolderRadialRedistribution.draft.lean`. It proves
the two-branch redistribution and the exact combined scalar constant
`2*exp(2*rho)*R(rho)*(3^(1-alpha)+3*rho)`. It does not bound the literal
complete summand: the endpoint transport exponential remains intentionally
outside this helper until its own signed contour has been constructed.

H2c is now written statically in
`tmp/BalabanCMP89Eq249ComplexHolderAliasSummation.draft.lean`. It applies the
sealed finite-product theorem to the single H2b source weight and produces
the literal one-dimensional `tsum` to the fourth power, uniformly in the
finite alias cutoff. The strict threshold `alpha < 1` remains visible. This
still does not bound the complete complex summand because the transport phase
is intentionally deferred to H3/H4.

### H3 — physical seam and one complete-integrand product contour

Prove the displayed and stabilized seams at general `alpha` with the physical
wrap `2*pi*L^j`.  The wrap acts on both physical integer displacements
`x-x'` and `x'-y`, producing integer `2*pi` phases; it does not make each
individual `2*pi` reciprocal-alias phase equal to one.

Construct holomorphy on the same complete polydisc used by the value and D1--D3
branches.  The nonvanishing premise must quantify over the full polydisc, so
all partial four-coordinate contour stages are covered.  Shift the complete
integrand once in the signed direction of `x'-y`, as CMP89 printed p. 586
states; derive product integrability and the one-coordinate/four-coordinate
telescope internally without splitting the Holder difference into two
separately estimated endpoint integrals.

Static signature inspection fixes a mass boundary that the earlier contour
queue did not expose.  The sealed complete-integrand contour equalities all
assume `0 < mass`, whereas the D4 generated operator is literally specialized
at `mass = 0`.  They therefore cannot feed H5 by specialization.  This is not
a request for a mass limit: the mass-uniform denominator nonvanishing and
displayed-domain seam are already separate inputs, so H3 must be rebuilt
directly in the following finite queue:

```text
H3a  complete-integrand differentiability on the full mass-uniform polydisc
     plus the displayed boundary seam, with no positive-mass premise;
H3b  one-coordinate complete-integrand contour shift from H3a;
H3c  four-coordinate product telescope, preserving one chosen endpoint and
     the complete Holder numerator throughout;
H3d  normalized complete-integral bound from H3c and the H2d pointwise bound.
```

The first H3a draft exposed a second, independent unit gate before H3c was
written.  Its seam used `cmp89Eq251LatticeDisplacement`, while the literal H5
integral uses `(L^j)^(-1) * u`.  The existing fine-lattice endpoint period is
only an `alpha = 0` theorem and cannot certify the complete Holder numerator.
That first four-file overlay, manifest
`C72245884ED54BF5360C81F5A423D46BA101DA29EF7CAE5497C998568FECB44F`,
is superseded static evidence and must not be promoted.

The replacement begins with the seven-declaration source/audit pair
`tmp/BalabanCMP89Eq249FineLatticeCompleteHolderPeriodicity.draft.lean`.
It keeps both the Holder and transport phases at physical spacing, proves
their centered-alias wrap period at general `alpha`, lifts the displayed sum
period through the literal non-singular domain, and has source/audit SHA256
digests
`469141764CD7B59DC1DA88FBACE880DBDF107EE24C50C5D4F80C23DBA1D1E2BD`
and
`47F161912BF553541ADDF118BE771BD95818CA5E3CDA841C55F0FA93EC78CE8A`.

H3a and H3b are then the source/audit pairs
`tmp/BalabanCMP89Eq251CompleteHolderMassUniformHolomorphy.draft.lean` and
`tmp/BalabanCMP89Eq251CompleteHolderMassUniformOneCoordinateContourShift.draft.lean`.
Their replacement source/audit SHA256 digests are, respectively,
`F4DE9EE49DAEFE33D3D62323EB0801348A832606A054488A54306012F447D67A`,
`90FC872A8F86669C0D2F980F4DB69715F58B5CD06C8A9312BDE134F5CBD89344`,
`1A0218BDF18BBC86437AEAC3DFCFA2453DE0125B8F6B553ED4164B8E17CD68CA`
and
`4A558E8D29C68DAD11F1CA7B50330BF71AEC18D786F9ABD5C8906698817581BE`.
The holomorphy theorem is generic in the two real displacements; the seam and
one-coordinate shift specialize both to physical fine-lattice data.  The H3a
nonvanishing premise ranges over every coordinate of the complete polydisc, so
the mixed intermediate stages of H3c are covered.  No source contains a
positive-mass premise or placeholder; none has been elaborated.

The deterministic six-file PRE-VALIDATION overlay is
`tmp/step8b24-c6c1-h3-mass-uniform-contour-overlay`, with manifest SHA256
`D887872AF1D88F8139A590FF07AC1F35F4D787C2BF984D0DDB9767F26830BC89`.
It records ten declarations and ten intended axiom readouts, requires both
fine-lattice displacements literally, and keeps the product telescope,
normalized integral bound, owner metric, `B0`, window 15 and terminal fields
open.  The preparer and fail-closed self-test are
`tmp/prepare_step8b24_c6c1_h3_mass_uniform_contour_overlay.py` (SHA256
`E55777411FE1396C50A7C2468D0E7068071CAEC71A497E03DBA5F39D1ABD4C21`)
and `tmp/test_step8b24_c6c1_h3_mass_uniform_contour_overlay.py` (SHA256
`08CA95060722F50E63A32CCD067950B71B1CEADA741F86B13EC541D25828D8AD`).
The self-test passed in 0.056 seconds at 20,742,144 bytes peak RSS, including
an explicit rejection of unit-lattice substitution.  The guarded
promoter is `tmp/promote_step8b24_c6c1_h3_mass_uniform_contour.py` (SHA256
`239925437DAEFC8003CF581269452D9DF0760EC598A349A4E7E6F9FD24051BB9`).
Its current dry run stops, before any write, at the first missing sealed
prerequisite `BalabanCMP89Eq248GreenMassUniformHolomorphy`.  Thus
`compiler_verified` remains false and H3c/H3d remain design obligations.

H3c is now also written, but deliberately not folded into the H3a/H3b overlay,
as `tmp/BalabanCMP89Eq249CompleteHolderMassUniformProductContourTelescope.draft.lean`
with its audit.  Their SHA256 digests are
`09A0AFFCECE4A978E94EF50A269BDCDD63CB3328612DEAE4DCADA34E71840B11`
and
`99E6B95D1BF6409AE778E0729A35F9A2FE48C34FABC1CEE1790B7B2D45276FA2`.
The five declarations construct partial-stage integrability, each coordinate
transition, the four-step telescope and the exact real-to-signed product
integral equality.  The contour sign is taken only from the physical
`transportU`; the physical `holderU` remains inside the same complete
integrand.  Static delimiter, placeholder, declaration-count and intended
readout gates pass, but the file is unelaborated.  Its separate deterministic
two-file PRE-VALIDATION overlay is
`tmp/step8b24-c6c1-h3c-product-telescope-overlay`, manifest SHA256
`35A3A58C2986B5074ED9AB2023259699B3DAB981A98F90CEC6D96BA7079D3CC3`.
The preparer, fail-closed self-test and promoter SHA256 digests are
`45BA3ED834BEF1D9372113257E17F31E16CC8EF5AB4C8D307953C6478ADF8C5B`,
`EE347204F86119A38F53284C2B189A643C3DFAEE53A9C51E785AA54A49AB8105`
and
`E6667EDABDBAA74CB500F0C1D8522C33110C1BF7E89E079D7F2841705FB5162F`.
The self-test passed in 0.040 seconds at 20,500,480 bytes peak RSS, including
explicit rejection of a contour direction taken from the Holder rather than
transport displacement.  The promoter stops before writing at the missing
sealed H3a prerequisite.

H3d is now written statically as
`tmp/BalabanCMP89Eq249CompleteHolderMassUniformNormalizedIntegralBound.draft.lean`
with its one-readout audit.  Their SHA256 digests are
`493FA9C8C7D5A14A8B30C2B25E20F8642C225A09B5E6B7E8604A69A4E219B2C5`
and
`B9A6E8BB4E85EF5203E4B7BE4DBFE9DCD5314E2A334BA992320748ACC76B120F`.
It composes H3c with the source-normalized Brillouin integral and H2d, so the
cube volume cancels exactly and the conclusion retains the literal physical
decay
`exp(-rho * displacementL1(xi * transportU))` and the named H2d constant.
Its deterministic two-file PRE-VALIDATION overlay is
`tmp/step8b24-c6c1-h3d-normalized-bound-overlay`, manifest SHA256
`84186FBFD6A1CC028F853E837AB03BF6D785C933EFF1AC201F09B59E93D9C06A`.
The preparer, fail-closed self-test and promoter SHA256 digests are
`E49764ECA0F19D28E5F6583655FB1F3ADC4F7A9A33FA83C30DE8C665C7283823`,
`815C3263DBDA0DBB238AE6A96BEFEE8300CBA64F60FE7D2B0747768E714AED41`
and
`D9BF88271269F8DE2B0AAD701EA3F78A80BA4CCEA01F1F93311B0719E8BDC01D`.
The self-test passed in 0.034 seconds at 19,910,656 bytes peak RSS and rejects
both a positive-mass premise and erasure of the physical decay.  The promoter
stops before writing at the missing sealed H3c prerequisite.  No compiler
verification is claimed.

### H4 — normalized nearest-endpoint contour and decay

CMP89 printed p. 585 assumes `|x'-y| <= |x-y|`, and p. 586 identifies
`|x'-y| = dist({x,x'},y)` under that choice.  Construct the finite-torus
nearest-endpoint selection explicitly.  The signed coordinate contour already
constructed in the repository produces the integer `l1` exponent
`cmp89Eq251LatticeL1Length`; the primary pages 585--586 do not, by themselves,
establish that this is definitionally the norm denoted by the source's bars.
Therefore the first selection is contour-optimal in signed `l1`, while the
identification/comparison with the printed two-point `dist` is a separate open
metric dictionary.  If the selected endpoint is `x` rather than `x'`, first
use a named swap/antisymmetry identity for the complete normalized difference;
do not silently rename the two endpoints.

This source reading was visually reconfirmed on 2026-08-17 from
`tmp/cmp89-primary.pdf` (SHA256
`416E2B1F00B52E7235AB27D2BE066B50D42DDE33CF8596BAEAE0A6688B145143`).
Printed page 585 displays the complete quotient in (2.49) and states the
assumption `|x'-y| <= |x-y|`; printed page 586 says to shift the integration
domain in the direction `x'-y` and writes the resulting factor as both
`exp(-delta0*|x'-y|)` and `exp(-delta0*dist({x,x'},y))`.  The render therefore
confirms the endpoint choice and single-contour direction.  It does not define
the bars as the repository's signed integer `l1` length, so H4d remains a real
dictionary rather than a definitional rewrite.

Apply the single complete-integrand contour of H3 in the selected direction
and cancel the literal external `(2*pi)^(-4)` normalization against the exact
translated Brillouin volume.  The output must keep the source quotient
`|x-x'|^(-alpha)` literal, retain one common positive strip radius, and produce
decay in the distance from `y` to the two-point set `{x,x'}`.  No triangle
bound on two independently shifted endpoints is source-faithful here: it
would discard the numerator cancellation before the Holder division.

H4 has four finite subbricks:

```text
H4a  choose the shorter signed-contour transport in lattice l1;
H4b  prove exact swap/antisymmetry of the complete stabilized integrand;
H4c  apply H3 once in the chosen endpoint direction;
H4d  expose the literal l1 minimum, then prove the separate comparison with
     the source/owner two-point distance used by the consumer.
```

The swap theorem is not an abstract renaming.  With

```text
h = x-x',       t = x'-y,
h_swap = -h,    t_swap = h+t = x-y,
```

it must prove, first branchwise and then for the stabilized full integrand,

```text
integrand(-h, h+t) = - integrand(h, t).
```

The equality follows from the literal phase identity

```text
(exp(-I*q.h)-1) * exp(I*q.(h+t))
  = -((exp(I*q.h)-1) * exp(I*q.t))
```

together with `||-h||_2^alpha = ||h||_2^alpha`; the derivative symbol,
averaging amplitude and stabilized denominator are endpoint-independent and
must remain syntactically the same.  The already sealed
`cmp89Eq251_phaseDifference_mul_transport` and
`cmp89Eq251_phaseQuotient_mul_transport` are reusable algebraic inputs, but
the repository currently has no named theorem for this complete swap.

The contour selection must compare the two *literal integer-lift* lengths

```text
cmp89Eq251LatticeL1Length t
cmp89Eq251LatticeL1Length (h+t)
```

and expose their minimum.  This is a theorem about the signed contour, not yet
an identification with the bars in CMP89 p. 585.  It must not select by
`finBoxDist` and silently identify that Chebyshev distance with the
signed-contour `l1` exponent.  The
existing theorem
`cmp89Eq251LatticeL1Length_add_le_add_one_of_unit` and its visible `exp rho`
corollary compare the two endpoint weights for the older independently
shifted route; they do not construct the nearest endpoint and cannot discharge
H4a--H4d.  Only after H4d has produced the literal minimum may the later
source/owner metric dictionary compare it with the repository's torus/owner
metric and justify labeling the result as the printed two-point distance.

The current H4a/H4b draft was audited branch-by-branch on 2026-08-17.  In the
`length(t) <= length(h+t)` branch it keeps `(h,t)` and orientation `+1`.  In
the complementary branch it selects `(-h,h+t)` and orientation `-1`; the
proved antisymmetry then gives

```text
original(h,t) = (-1) * integrand(-h,h+t).
```

Thus the selected transport length is literally
`min(length(t), length(h+t))`, including the tie convention, and the original
ordered normalized difference is reconstructed exactly.  No endpoint label is
renamed and no metric comparison is used.  This is still a static semantic
audit of `BalabanCMP89Eq249CompleteHolderEndpointSwap.draft.lean`; compiler
verification remains pending behind its declared prerequisite queue.

A deterministic two-file PRE-VALIDATION overlay for this H4a/H4b subbrick is
now prepared at `tmp/step8b24-c6c1-h4-swap-overlay`.  Static composition with
H3d exposed the same unit mismatch as H3: the first version reconstructed the
integrand at unit-lattice displacements.  That overlay, manifest
`B0271350BC3310227A3A0990AE49B6A9B0F71E20EAB5DAD43E35675B315FC241`,
is superseded and must not be promoted.  The replacement theorem keeps the
integer `l1` comparison only for branch selection and reconstructs both
integrand arguments literally at `xi * u`.

The replacement manifest SHA256 is
`A8EC12904CB695C8EB1258D6FA3B6BB010BD907EBC8F39C3433E9AD5672E0DC9`;
the promoted source/audit blob hashes are respectively
`BD7E8891736D5068F39F6AEBBF136A1D9E4B3EBE16F29B3CDCC2A6A359D10531`
and
`1FD2C481BC3735224C2DF4ACAC732BE34D5E8794935E990B6851FC6B36C6D980`.
The generator and fail-closed self-test are
`tmp/prepare_step8b24_c6c1_h4_swap_overlay.py` (SHA256
`591D4664E2429ED89A32CAB163A3E7455EFE1FBDB6366CECE066D52C782E6B0F`)
and `tmp/test_step8b24_c6c1_h4_swap_overlay.py` (SHA256
`CEEA7B0A18EBEDD04568D1718EE4DF3A364E93683B9F573A9DB1D2175980A1BC`).
The self-test passed in 0.030 seconds at 20,365,312 bytes peak RSS, including
explicit rejection of unit-lattice substitution.  The overlay
has not been copied into the tracked tree and has not been elaborated by Lean.
The future Colab unit is generated only after a source checkpoint contains
those exact promoted blobs by
`tmp/generate_step8b24_c6c1_h4_swap_validation_runner.py` (SHA256
`6BE94687A9B7A7A7AE0BCAAB48F5273573D3990EDD3982D436CE3105CFE61BB1`).
It pins both git blobs, runs one focal followed by the six-readout audit, and
keeps the CMP95 carrier, metric dictionary, H4c/H4d, `B0`, window 15 and
`TermSource` explicitly open.  Its generator self-test (SHA256
`A12970219298679EB403F8A8579F01842B21F5317719C03F37216193C3242CF8`)
passed in 0.011 seconds at 21,016,576 bytes peak RSS.  No runner has been
generated against the current commit because the overlay is intentionally not
tracked yet.
The mechanical promoter
`tmp/promote_step8b24_c6c1_h4_swap.py` (SHA256
`0466552B446C2C73A5EB17D554BF16C840FB5287054C5A3ACA5C8A232800A936`)
requires both direct imports and their audits to be sealed and present in
`YangMillsCore`, checks the exact manifest and both blob sizes/hashes, and
writes only the two PRE-VALIDATION targets.  Its replacement dry run passed on
`b05ef65af97a95752d1c929e30749d886d425d8d`; `--write` was not used.

H4c is now written statically as
`tmp/BalabanCMP89Eq249NearestCompleteHolderNormalizedBound.draft.lean`
with its audit (SHA256
`222C0061CF07F1F2CDBAA1329C5A4EE33FAE1338D02ECF11985F0828BB70C8CD`
and
`9C1B60A56EB202178C7EC8FD83D2BA07CAF15F2A4E66AC75A803478E0518E5D3`).
It derives the selected Holder edge unit internally, lifts the exact
orientation identity through the normalized integral, proves that the
orientation has norm one, and applies H3d exactly once.  It never adds two
endpoint estimates.  Its conclusion remains in the literal physical
signed-`l1` decay at the selected transport displacement; the H4d owner-metric
dictionary is still open.  The deterministic overlay is
`tmp/step8b24-c6c1-h4c-nearest-bound-overlay`, with manifest SHA256
`F650C9E28ACA8EDCD9C0A85C4AAAA4A0B249A43438653CFE81018FD4A01D78BE`.
The preparer, self-test and promoter have SHA256
`E1E1CC72D03E7C4E54E827B4565EC8066D417ECBB56EE9283DF4D1C40148733F`,
`E7AB7B36D1A442F6B725E4DD04EA7E687325E966EA3507DC14FEFD52394CD124`
and
`E26C52444E62C86C58CB0538A73A92242978691D3BEE67F53CA56D1D7BA8BDDD`.
Its self-test passed in 0.038 seconds at 20,295,680 bytes peak RSS; the promoter
stops at the missing sealed H4a/H4b prerequisite.  `compiler=false` remains
explicit throughout.

The H4d metric endpoint is now reduced statically in
`tmp/BalabanCMP116CMP89PhysicalNearestEndpointOwnerTransport.draft.lean`
with its audit (SHA256
`BC0D5ABF811615DE9A042EAF2B0B2891B6A0E1F30E9FB53689C5B1FBEF3D97B9`
and
`74C4FC974432C4B0E4A084368F66B2F7CA0A918D1C3E270E4B95229F6AA49667`).
It does not reuse the old target-only two-endpoint estimate.  Instead it
proves that the seam-safe integer lift of the first endpoint dominates its
own fine-site distance, keeps the source and target owner comparisons
separate, and only then takes their minimum according to H4a's internal
endpoint choice.  Consequently one selected contour gives one owner decay;
there is no `1 + exp rho` endpoint-sum factor.  The exact two-corner boundary
cost and the H2d amplitude remain visible.  The same comparison accepts any
integer lift carrying an explicit proof of the correct periodic projection;
therefore H5's affine zero-residue lifts do not require a second metric
identification.  Its deterministic overlay is
`tmp/step8b24-c6c1-h4d-owner-transport-overlay`; manifest SHA256
`1B3A686E649F9636AD6AF613313F0EB7E1A6131A95B0280B52FDC3BE4D14B1A3`.
The preparer, self-test and promoter have SHA256
`F7D694DF853CB3542EA8F61300CC832C40AE2312FEE4D0B2CAF8104BC6AFDAD7`,
`72804B0B299A430726B3967A163043CB5A16BB6670DEA80575A72128AC7BB1FD`
and
`85F163006DA87277E734F934209B511F16A5B0E579EF0575F49AF8F185923796`.
The self-test passed in 0.045 seconds at 20,471,808 bytes peak RSS; the
promoter stops at the missing sealed H4c prerequisite.  This remains a static
interface: its nine declarations and nine oracle readouts have not been
elaborated, and regional `B0`, window 15 and every terminal field remain open.

### H5 — generated operator and owner transport

Use the D4 generated left-derivative identity at `x` and at `x'`, then form
their difference and divide by the physical distance before estimating.  The
two point-source identities, target-seam reindexings and zero-residue sums must
be constructed, not accepted as an equality to a free operator family.

A static interface audit on 2026-08-17 reduces this to the following finite
subqueue.  D4 already constructs, for every target `x`, the exact zero-residue
series

```text
sum_n centeredLeftDerivativeCoefficient(u_x,n),
u_x = -fineToCoarseEndpointDisplacement(x,y).
```

The coefficient is definitionally the normalized fine Fourier left-derivative
kernel evaluated at `residueAffineMap M u_x n`.  The existing sealed theorem
`cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_fourierLeftDerivativeDiff`
also identifies the complete normalized Holder integral with a difference of
two such kernel values.  It cannot, however, be used for the physical D4
specialization: its signature assumes `0 < mass`, whereas D4 is literally at
`mass = 0`.  Substituting the sealed theorem here would therefore reintroduce a
mass premise that the mass-uniform route was built to remove.

The remaining H5 bricks are:

```text
H5a  mass-uniform real-slice recombination at alpha = 0:
     prove at mass = 0 that the source-normalized raw endpoint-difference
     integral is the difference of its two left-derivative endpoint kernels.
     Here "normalized" means the external Brillouin-volume factor, not Holder
     normalization.  Use the mass-uniform integrability/nonvanishing queue;
     do not take a mass limit and do not assume 0 < mass.

H5b  affine-residue target dictionary:
     specialize to the actual positively oriented `PhysicalBond`, so
     `target = source.shift bondNu`; no arbitrary-pair residue equivalence is
     needed here.  Cite the D4 target-carry equivalence to rewrite the target
     zero-residue series as the ordinary forward shift of the source series.
     More precisely, keep the derivative direction `derivMu` independent of
     the bond direction `bondNu`: the target shift and residue carry use
     `bondNu`, while the Fourier derivative symbol keeps `derivMu`.  The
     physical Holder displacement is `source - target = -e_bondNu`, proved by
     `cmp116CMP89PhysicalBondHolderDisplacement_apply`, including at the seam.

H5c  termwise exact bridge:
       coefficient_derivMu(source,n) - coefficient_derivMu(target_reindexed,n)
         = rawAlphaZeroIntegral_derivMu(
             -e_bondNu,target_reindexedResidue).
     Equivalently the D4 forward difference is the negative of the raw
     physical-bond integral before H5d0 installs the Holder power.  This sign
     is forced by the source-minus-target bond
     convention; it must be stated as an equality and may not be normalized
     away by swapping endpoint labels.  The proof is H5a plus H5b, not a bound
     and not a supplied operator dictionary.

H5d0 physical Holder normalization:
     prove the exact equality between `xi^(-alpha)` times the H5c raw
     `alpha = 0` integral and the complete `alpha` integrand/integral for the
     physical bond.  Construct `||xi*(-e_bondNu)||_2 = xi` from the sealed unit
     bond and positive fine spacing; do not absorb `xi^(1-alpha)` or move the
     division past a norm.

H5d  generated point-source Holder identity:
     use D4 absolute summability, its exact forward-difference series,
     `tsum_neg`/`tsum_congr`, termwise H5c and H5d0 to identify the physical
     source-minus-target difference of the two internally generated
     point-source derivatives with the zero-residue sum of complete Holder
     integrals.  The derivative contributes `xi^(-1)` and the Holder quotient
     contributes the separate literal `xi^(-alpha)`; both occur before any
     norm.  No subtraction of two D4 endpoint bounds is admissible.

H5e  owner transport and arbitrary localized source:
     first sum the complete zero-residue family to the one centered-periodic
     endpoint weight using the sealed exact residue theorem; then apply the
     single-contour H4 bound once to that centered representative and
     transport the literal minimum endpoint length to the minimum of the
     source- and target-endpoint owner distances produced by H4d.
     Extend from one point source to one identity-owner fibre without a fine
     volume or source-cardinality factor.
```

H5e is further split, before implementation, into four fail-closed bricks:

```text
H5e0 zero-residue affine projection:
     prove that `affineResidue ell forwardU n` projects to the literal
     target-minus-blockBasepoint endpoint whenever `n` belongs to the zero
     residue subtype.  The proof must use the divisibility/quotient theorem
     for that subtype and the sealed target-wrap carry; membership alone may
     not be erased by simplification.

H5e1 carrier-presentation dictionary:
     transport the D4 carrier `ell*(2*(K*Q))`, its physical bond and the
     canonical `blockBasepoint ell (2*(K*Q)) y` through
     `cmp99Eq389SourceLocalizationSiteEquiv.symm`.  Prove preservation of the
     positive bond target, shift and owner, and prove that the owner of the
     transported block basepoint is exactly `y`.  Do not identify the two
     propositionally equal carrier products by `rfl`.

H5e2 residue-family owner estimate:
     use
     `tsum_norm_cmp99FlatIntegerZeroResidueClass_le_centeredPeriodic` to
     consume the complete zero-residue family while retaining exactly one
     centered-periodic endpoint weight.  Use H5e0's centered cast and H5e1's
     carrier dictionary, then apply H4d's `_of_cast` theorem once to that
     centered representative.  Do not split the decay rate termwise: doing
     so erases the residue decay and makes the resulting tsum diverge.  The
     accepted route introduces neither a representative prefactor nor a fine
     cardinality.  The H2d amplitude and two-corner boundary factor remain
     separate.

H5e3 source extension:
     combine H5d3 and H5e2 for one point source, then extend over one
     identity-owner fibre.  The extension must use the already named owner
     fibre decomposition and may not insert a count of fine sites or replace
     the two-endpoint owner minimum by the target owner.
```

The need for H5e0 is now reflected directly in H4d's interface: its generic
metric and exponential theorems accept an arbitrary integer transport lift
only together with the coordinatewise `ZMod` projection proof.  The centered
physical displacement is merely a corollary.  Thus H5e0 is a concrete proof
obligation rather than an implicit convention.

H5e0 is now written as the three-declaration static source/audit pair
`tmp/BalabanCMP99SourceSeparatedPhysicalHolderResidueOwnerProjection.draft.lean`
and its audit, with SHA256
`6A9671EF28C5D8BC88D5C599C644D2C3F0B04D89BD7FBA34E49E2FF405AEE29F`
and
`EB2E12CF7D3ECADC2B7D1290244241520D199755E54C08C04C29D10545DE06CD`.
It consumes both the target-wrap residue equivalence and the named
zero-residue quotient reconstruction before casting into `ZMod (M*N)`, and
then proves the corresponding cast theorem for the canonical centered
periodic endpoint representative.  This is the exact projection bridge used
after the residue family has been summed, rather than a termwise rate split.
Its deterministic overlay is
`tmp/step8b24-c6c1-h5e0-residue-owner-projection-overlay`, manifest SHA256
`46AC30FE60920AC8B4C158A6880FD6B73D3AF90C0866DA6A0CAFEFF0F1420DBC`.
The preparer, self-test and promoter SHA256 values are
`4CDAF4F0B62BFB93B7674043DC53390209D17218E484DA3729B30A8AABE79939`,
`D29FC838757C8246A0196ADD056090D4B6D889720F905C5E97B4204C7451317F`
and
`B82AFB3D822C799D030C189FCA557FC8EE1AB7E402DE03D855640C8303AC68B5`.
The self-test passed in 0.038 seconds at 20,156,416 bytes peak RSS; the
promoter stops at the unsealed D4 residue-shift prerequisite.  No carrier
presentation, owner estimate, regional `B0`, window 15 or terminal field is
claimed.

H5e1 is now written as
`tmp/BalabanCMP99SourceSeparatedPhysicalHolderCarrierDictionary.draft.lean`
and its audit, with SHA256
`31BD90EF4C1798FD2DB5380E9CB6A3CE4C5DDCC23673C88791B5A8F3480C4E0F`
and
`E33884A7DD491AB0F1CF15D9B09B7104E391ED91A32DF4E0593D31D81F3B8553`.
Its five declarations expose the dependent cast, prove that it commutes with
the positive step, transport the physical-bond target, and identify the owner
of the transported canonical block basepoint with the original D4 coarse
site.  Its overlay is
`tmp/step8b24-c6c1-h5e1-carrier-dictionary-overlay`, manifest SHA256
`F6C7A460F696CEF6441C18395858E705ACFCF0149DBEBC9EACA44DDD70891AE5`.
The preparer, self-test and promoter SHA256 values are
`09534D5CDC1323C5B7EAD48561D4ED3D6B799552BA6648A6668F5EAA0BE9D6E0`,
`B51BA6404306315ED30CC03ACD092BFA82D61CB0853E09DA9AC308D56B83D9B1`
and
`8D885465D6B6D0D01B79B10F51E4FF7AE598858012C3736E40E7FE7A0502357B`.
The self-test passed in 0.030 seconds at 20,099,072 bytes peak RSS, and the
promotion dry-run passed on `b05ef65af97a95752d1c929e30749d886d425d8d`.
`--write` was not used; compiler verification, metric bounds, `B0`, window 15
and terminal fields remain open.

H5e2 is now written statically as
`tmp/BalabanCMP99SourceSeparatedPhysicalHolderResidueFamilyOwnerBound.draft.lean`
and its audit, with SHA256
`D210EA5BB44695B7A3D1C5E31D9A01D0076A2E75A5F532BE8043F7A89F1D5AE3`
and
`CB8ED17FA5CC9E4F72FCC03B5E1DA505D8A7689746537F8AB36EDA73D6FC1F2F`.
Its one theorem first applies the exact zero-residue `tsum` bound to the
target-based complete Holder coefficient, leaving the canonical centered
endpoint.  It then uses H5e0's cast, H5e1's carrier presentation and H4d's
two-point owner theorem once.  The intermediate inequality from the centered
target weight to the internally selected nearest-endpoint weight is the
literal `min_le_left`; no rate split, representative multiplier or fine-site
cardinality occurs.  This is a static candidate, not compiler evidence.

Its overlay is
`tmp/step8b24-c6c1-h5e2-residue-family-owner-bound-overlay`, manifest SHA256
`819A26F4351FA04D3861B947584B486F54F4F83C71BC79F0F2E2B974A47FCA46`.
The preparer, self-test and promoter SHA256 values are
`9271A06A9D7602DF5716C9E1855864F4693994241030B77B391C9E5FF4391123`,
`46B9AF452FAD52DE82BF0EE929F3AA9D3E64BCABF9E0E2119E628ABF669FBE37`
and
`4BBA3D20F3E9FD1BA328E17D8602AF3A822886EBAEE5CC695EF46B8CDA6985E9`.
The self-test passed in 0.012 seconds at 18,526,208 bytes peak RSS; the
promotion dry-run stops at the first unsealed H3d complete-Holder-bound
prerequisite and writes nothing.  Regional `B0`, source extension, window 15
and terminal fields remain open.

The point-source half H5e3a is now written as
`tmp/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolderOwnerBound.draft.lean`
and its audit, with SHA256
`D8E826E4B7E0AA99E6F3DEA8DF77F97C0967067A45FF80C28A98AE7C4F6CCDBD`
and
`AB21AB30832BFE13A8965304360F45C42A5124B7FF68F75E7ED6654A6717863B`.
It reconstructs absolute summability from the two derivative coefficient
families and the exact termwise Holder identity, applies
`norm_tsum_le_tsum_norm`, and then combines H5d3 with H5e2.  Its deterministic
overlay is
`tmp/step8b24-c6c1-h5e3a-point-source-holder-owner-overlay`, manifest SHA256
`5C4FA90BBD391ECB0C955CBE5BA858E286466CB57EB80C95CB31FFC2C377A1D5`.
The preparer, self-test and promoter SHA256 values are
`7860CC9239997EFA9A5FB4DAAB08253A239FA89FF8CEB7D2FD3C7C381DDD59A5`,
`BBF42847F0F3001DAB40EBBAB79A66F2EED1252EEAE7BD700360356A7FA4D482`
and
`2CAB0F8A10D99271FAE74A410FFC910896963A3815A2FC388AD000C22ECCCB3E`.
The self-test passed in 0.008 seconds at 18,116,608 bytes peak RSS.  The
promotion dry-run stops at the first unsealed H5d point-source prerequisite
and writes nothing.  It remains a static, unelaborated candidate; all
compiler evidence remains open.

H5e3b is now written statically as
`tmp/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldHolderOwnerBound.draft.lean`
and its audit, with SHA256
`E07BB8D1656734F87AEC9F6F08E26D3360A036AACC04EAD6413F86C2D1B49D51`
and
`90F774C5C8196817D2A203077C798FE991C4F76CBF6749E7D989088CF9C58FDD`.
It defines the literal generated derivative on an arbitrary coarse field and
uses the already named identity-owner reduction to rewrite that field to one
point source.  H5e3a is then applied and `norm_apply_le_finitePiLpSupNorm`
closes the source norm without an owner-fibre or fine-site count.  The full
constant remains visible in the conclusion.

Its overlay is
`tmp/step8b24-c6c1-h5e3b-localized-field-holder-owner-overlay`, manifest
SHA256
`F45C97E9EB9E81E70DCDE6FDE6765CBDD6B2CDF9E20D63CF553E3116641EAED3`.
The preparer, self-test and promoter SHA256 values are
`7C6A3611B241B303EC62DA3DD38315FB65D3FE84F5B616006DE08518EF22674D`,
`C2F9B624E8C24C424C9788DB2B6BF583E8EE0B8BE3610CF107D3536421488FFA`
and
`34402D456E81158DB8990A61E5F092BCD70A9B5B59B887C1E2B8BFD86D7802BB`.
The self-test passed in 0.010 seconds at 18,116,608 bytes peak RSS; the
promotion dry-run stops at the unsealed H5e3a prerequisite and writes
nothing.  It remains unelaborated and supplies no regional `B0`, window-15
attainment or terminal field.

This audit also fixes the dependency direction: H4c/H4d and H5a precede the
generated-operator estimate.  D4 supplies the exact operator series, but its
pointwise owner bound is not an input to H5 because using it twice would erase
the Holder numerator cancellation.  H5a is a mass-uniform real-slice
integrability and algebra statement, not a new contour theorem; H3/H4 supply
the single complete-integrand contour.  All target seam and point-source
algebra must be inherited by name from D4.

H5a is now written as the static two-file draft
`tmp/BalabanCMP89Eq249MassUniformRealSliceRecombination.draft.lean` and its
audit.  The source and audit SHA256 digests are respectively
`9A38D0E4277A035C902206B984620106DBBD36881308778B528D59CB8366B5AA`
and
`BB12D95F380B1BE43992588F6733CE2789C2BE748FD8C412A5E33787EDDF65E8`.
It derives real-slice integrability from the prepared mass-uniform D3 product
integrability at stage zero, recombines the complete integrand pointwise, and
then uses the already sealed endpoint-to-kernel identity.  It contains no
placeholder and no positive-mass premise, but remains unelaborated and must not
be promoted until D3 has its own cold seal.

The H5b/H5c raw termwise algebra is now written separately in
`tmp/BalabanCMP99SourceSeparatedPhysicalHolderTermwiseBridge.draft.lean` and
its audit (SHA256
`8DE98F2CB90E096554E2372B7D2FBAFB0F22519B52297C72242F8F0306CE771E`
and
`22CBFB16189C01FAE1ABC02E9C1104C42F4627A4B447CC9EB2A4DC60BE26261B`).
It proves the negative-unit-plus-forward-residue identity and then derives the
source-coefficient-minus-reindexed-target-coefficient equality from H5a, with
independent `derivMu` and `bondNu` indices.  Its integral is explicitly still
the raw `alpha = 0` object; H5d0 must install `xi^(-alpha)`.  It does not perform
the D4 `tsum` transport and remains an unelaborated static draft behind H5a and
D4.  The earlier same-index draft/manifest was rejected and superseded before
promotion.

The four H5a--H5c files have a deterministic PRE-VALIDATION overlay at
`tmp/step8b24-c6c1-h5-termwise-overlay`.  Manifest SHA256 is
`826C1D7567A949FE6E212CC61E053C3009C69AF94A394144158B269782C40640`;
the promoted blob hashes, in source/audit/source/audit order, are
`A5AC55B4F6442889A72E5AE5AC2F5E3B7AEF7E30DAD23E029E69A10DCC382AD3`,
`84DE542354F34834AD6B19407CFFFB505B8D06E2359BCE30ABFF800AB3BB979F`,
`5FDF2C4E215B5E01F54AA8DD20A8E229D0E6A870844E2F0CDB4E2B5C2D915F69`
and
`0E063710C8EB8A2AE5686DB8D7E58BEF3F5719D4B9D4EB0BA0A1B92F27A6625B`.
The preparer and its fail-closed self-test have SHA256
`0B2DF4886EAF106E41D6ED2ADBE74E4EA145DA6777EEF3DD3DFCF301A4B88E74`
and
`7A84ADFBDDB0C3E7F2AE96EAE587A10633D6F359F304634BA33BF411F83B80D5`.
The self-test passed the positive path and explicit `sorry`, positive-mass,
independent derivative/bond direction, missing-readout and input-hash tamper
gates in 0.020 seconds at 19,943,424 bytes peak RSS.  Overlay preparation
passed in 0.010 seconds at 18,886,656
bytes peak RSS.  These are mechanical checks only; `compiler_verified` remains
false and the manifest keeps `tsum`, owner metric, window 15 and terminal
fields open.

Promotion is guarded by
`tmp/promote_step8b24_c6c1_h5_termwise.py` (SHA256
`7217E5C3E3E04300FE00F6EBACE2B5960A7B8B6AFD285DB762F9457A302C5190`).
It requires the D3 product telescope, the sealed fine derivative kernel, D4c
periodization and the physical-bond dictionary together with all four audits
in `YangMillsCore`; it then verifies the manifest and all four overlay blobs
before writing.  Its current dry run stops, as intended, at the first missing
prerequisite:
`BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope.lean`.
No tracked file was written.

The pointwise part of H5d0 is now the four-declaration static draft
`tmp/BalabanCMP89Eq249PhysicalHolderAlphaFactorization.draft.lean` with audit
(SHA256
`A510FC96E3C55A473CD8E3F71BE79C8FB00327D0BAD88E44B239415098AE54F2`
and
`012C09CA5527B11594C434BC42207B8454176EFB4D661773B05F9DB961C1CF22`).
It factors the common Holder power first from each bare alias, then from the
central/noncentral stabilized numerator and complete integrand, and finally
specializes the factor to literal `xi^(-alpha)` using the physical unit-edge
norm.  It keeps `derivMu` independent of the bond displacement and does not yet
lift the equality through the normalized integral.  The draft is unelaborated
and depends on the future seal of the physical H1 phase/metric brick.

That integral lift is now written separately in
`tmp/BalabanCMP89Eq249PhysicalHolderNormalizedIntegral.draft.lean` and its
audit (SHA256
`714FCB23825810AC0748DA8C3CA22B05314E6A1D5E83725DDCA4C89D3462C3BE`
and
`BAE0B16BA2ADCAE3A3577D1E1CCFA3E59D2C8BA4CB57387F4710881CE108FBF1`).
It defines the literal general-`alpha` normalized Brillouin integral, proves
its `alpha = 0` specialization is the existing raw object, and uses pointwise
H5d0a plus unconditional `integral_const_mul` to extract the exact
`xi^(-alpha)` scalar before norms.  It remains an unelaborated static draft;
generated operators and `tsum` transport are not part of this brick.

The four H5d0a--H5d0b files now have a deterministic PRE-VALIDATION overlay
at `tmp/step8b24-c6c1-h5-holder-factor-overlay`, with manifest SHA256
`E5FCFA044FECE89BC64229D1D55DB5C2E4F2C68D752F0F38EAED4A6AFD69D2C3`.
It records seven declarations and seven axiom readouts and keeps the generated
operator, `tsum`, owner dictionary, window 15 and terminal fields open.  Its
fail-closed self-test passed the exact-alpha, alpha-zero, pre-norm extraction,
positive-mass, placeholder, missing-readout and hash-tamper gates in 0.031
seconds at 20,283,392 bytes peak RSS.  The preparer and test SHA256 digests are
`D00A4F2FF613DDC686537AA8228FEBEEBE6820AFEF3C9BD0A6EFE46BED1D355A`
and `B1C8BA1DE49ADA9F1FD83940011DCB885C67023FB248061F7CB27F8367D71A01`;
the guarded promoter digest is
`40C328BF12A80EA95FEEA6782103A24293C56E3B958091685760DD76AA16508F`.
Its current dry run stops at the first unsealed H1 prerequisite and writes
nothing.

The H5d generated point-source step is now fixed as three named equalities,
not as an endpoint-bound subtraction:

```text
H5d1 target derivative residue reindexing
  tsum_n coefficient_derivMu(u_(source.shift bondNu), n)
    = tsum_n coefficient_derivMu(forwardShift bondNu u_source, n).

H5d2 complete-integral tsum identity
  tsum_n holderIntegral_alpha(
      holderU = physicalBondHolderDisplacement(source,bondNu),
      transportU = affineResidue(forwardShift bondNu u_source,n))
    = xi^(-alpha) *
        (tsum_n coefficient_derivMu(u_source,n)
          - tsum_n coefficient_derivMu(forwardShift bondNu u_source,n)).

H5d3 generated point-source identity
  xi^(-alpha) •
      (generatedDerivative_derivMu(source, pointSource owner v)
        - generatedDerivative_derivMu(source.shift bondNu,
            pointSource owner v))
    = (tsum_n holderIntegral_alpha(...,n)) • v.
```

Here `generatedDerivative_derivMu(x,...)` already contains the separate
literal fine-spacing factor `xi^(-1)` from D4.  Therefore H5d3 must retain both
`xi^(-1)` and `xi^(-alpha)` before any norm.  The D4 identity is applied twice
with the same `derivMu`; only the outer physical endpoint and the residue carry
use `bondNu`.  H5d1 is the generic D4 carry equivalence specialized to the
literal derivative kernel.  H5d2 uses absolute summability of the two D4
coefficient families, H5c termwise, H5d0 before norms, and one exact
`tsum_sub`; it may not use the two pointwise owner bounds.  H5d3 then follows
from the two exact D4 point-source identities, H5d1 and scalar/smul algebra.
This decomposition makes the source-minus-target sign and the independence of
`derivMu` and `bondNu` fail-closed at each interface.

H5d1--H5d3 are now written as two static source/audit pairs:
`tmp/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalHolderTsum.draft.lean`
and
`tmp/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceHolder.draft.lean`.
Their source/audit SHA256 digests are, respectively,
`E8B8618F48FA0D2D43ACCB211C585BF3A866F57F9CC9B18417696F50026D677A`,
`BFF46296DC597E755A5BFA2962D4486A674ABE4DFA037FA82BF6A6117B1A02DA`,
`1F81EEE5722064193487F70FF5EE383246284619CD76CBD8B97AFF4772CA9BD7`
and `CAFFE5E2923A335A0F92E311584911DC06F5B45FA7A5A0CCA37DA1444C87391B`.
They contain five declarations and five intended readouts, no placeholders,
and balanced delimiters, but remain unelaborated.

The deterministic PRE-VALIDATION overlay is
`tmp/step8b24-c6c1-h5-generated-holder-overlay`, manifest SHA256
`3990E079577DB1272C9195AE7515FCA2B6D7B864C4020F340E941AEDDE06DFEC`.
Its self-test passed direction-independence, physical-target, pre-norm,
placeholder and input-hash sabotage gates in 0.043 seconds at 19,660,800 bytes
peak RSS.  The preparer, self-test and promoter SHA256 digests are
`9A42BDEA6FB6F6204B394B2C7AD93FC3D3FE9158EECA5374B4BE9A0A1CD636D8`,
`48267C970E0D8C1F1C0DA15667A1370237BC66B77F085872C615C46B63D89262`
and `723E3EC00BBFCBBEFD591049D3CBB5B722674C0E0697C546D6B1F7441F07A18A`.
The promoter requires all H5d0, H5c and D4 residue/periodization/point-source
inputs to be sealed and imported by `YangMillsCore`; its current dry run stops
at the first missing H5d0 prerequisite and writes nothing.

Transport the signed `l1` decay through H4d's literal two-endpoint owner
minimum without a fine-volume or source-cardinality factor.  Do not replace
that minimum by the target owner and do not reintroduce the old
`1 + exp(rho*xi)` endpoint-sum cost: H4c has already selected one contour and
H4d has separately controlled both branches.  The result remains
ambient/complex input for CMP95/CMP96; it is not regional `B0`.

## Source-fidelity gates

1. `alpha` is constrained by `0 < alpha < 1`; neither endpoint is smuggled
   through the weaker phase lemma.
2. The physical displacement is `xi*(x-x')`, never `x-x'` in unit-lattice
   units.
3. Every noncentral alias phase survives until a norm is taken.
4. The numerator cancellation occurs before division and before norms.
5. Central and noncentral branches stay separate until their exact finite sum.
6. Mass zero is an actual specialization using the mass-uniform reciprocal;
   it is not a limit and no `0 < mass` premise survives.
7. The complete Holder integrand receives one signed contour based on a
   constructed signed-`l1` nearest endpoint; endpoint exchange is a named
   theorem, and source-distance identification remains a separate dictionary.
8. The common radius/nonvanishing gate is on the complete polydisc, not one
   shifted coordinate with the others real.
9. Normalization, the factors `2` and `3^(1-alpha)`, the CMP96 scale
   `(L^j*eta)^(1-alpha)*(holderSeminorm zeta alpha + abs zeta)`, the half-rate
   `delta0/2`, and any one-link exponential cost remain literal.
10. No theorem is labeled as a field of (3.42), regional `B0`, window-15
    attainment or terminal progress before the CMP95/CMP96/CMP99 dictionaries
    are constructed.

## Dependency and promotion order

```text
Step 8b.23 A--F cold seals
  -> Step 8b.24 S1--C6b cold seals
  -> D1--D4 left derivative cold seal
  -> H1 exact physical normalization
  -> H2a global complex-strip phase quotient
  -> H2b physical local-pair specialization
  -> H2b radial product + exponent monotonicity
  -> H2c alias summation
  -> H2d central/noncentral recombination
  -> H3--H5 complete Holder contour queue
  -> C6c.2 literal C^(j) / common-majorant assembly
  -> C6c.3--C6c.9 regional transport and certificate.
```

The H3--H5 part of this order is now independently pinned by
`tmp/audit_step8b24_c6c1_h3_h5_schedule.py` (SHA256
`F604359A160B6B8E6B0142182F52A0C70A8ABEA2CFDDBF707707DA310F5EDFD7`)
and
`tmp/STEP8B24-C6C1-H3-H5-PROMOTION-SEAL-CHECKLIST.md` (SHA256
`7D34F16F610C229BE35A48CF92B77C97E90192B406C408502860FD2480B620DC`).
The read-only gate checks 14 exact manifest hashes, 38 disjoint overlay blobs,
65 manifest declarations, 60 intended axiom readouts and 39 internal import
edges.  It caught one genuine ordering error: H5's termwise/recombination
brick must precede the Holder-factor brick because the latter imports the
former's real-slice recombination.  With that correction the internal graph
is acyclic.  `--require-ready` currently refuses promotion on the exact ten
unsealed external producers listed in the checklist; this refusal is the
expected state, not compiler evidence.

The corresponding batch writer is
`tmp/promote_step8b24_c6c1_h3_h5.py` (SHA256
`20B84DC8B3CFBF8E6C705CC69B8315F10699991D91ED2ABE2A876AD0F0EB6E04`).
It allows PRE-VALIDATION dependencies only within this exact checked DAG and
requires every external producer to be sealed and imported by
`YangMillsCore`.  Its present dry run stops at the first absent external
producer and writes nothing.

The restartable diagnostic and one-cold-checkout workflow generators are
`tmp/generate_step8b24_c6c1_h3_h5_validation_runner.py` (SHA256
`EC2B096217A21C77BC794E266E5C5F5D724108D30D66A1F04421E0C882E8C190`)
and `tmp/generate_step8b24_c6c1_h3_h5_terminal_workflow.py` (SHA256
`4185431E767406298C76ED7921A9A5C3008F06126CC9BCC5EA5912616EB29C53`).
Their measured static gates agree on 38 files, 19 source/audit pairs, 38
stages and 60 axiom blocks.  The terminal generator deliberately refuses to
materialize a workflow before the promoted source checkpoint exists: every
input digest is read from the Git object with `git cat-file blob`, so neither
a fictitious SHA nor the CRLF worktree can become terminal evidence.

The primary CMP95 page gates the *local Holder-seminorm specialization*, not
all contour algebra below H3.  A static signature audit on 2026-08-17 found
that the following scratch subqueue does not mention a seminorm carrier or a
ready-made Holder bound:

```text
Eq248 Green one-coordinate shift
  -> Eq248 Green product-contour telescope
Eq249 left-derivative one-coordinate shift
  -> Eq249 left-derivative product-contour telescope
Eq249 complete-integrand endpoint swap / signed-l1 nearest-endpoint choice
```

These files use the already named common-radius, central-window, mass-window,
holomorphy and integer-endpoint data.  They may therefore be elaborated and
audited as cutoff-agnostic contour infrastructure before page 35 is acquired.
They must not, however, be advertised as the complete H3--H5 Holder result:
the theorem that inserts the physical local-pair quotient and the final CMP96
scale still depends on the visually confirmed CMP95 carrier.

This boundary is enforced by
`tmp/audit_step8b24_c6c1_contour_independence.py` (SHA256
`233C4FD7CB0E8E3D78E433D255B7BF228E1BDFCB194D190287A0BB9DF79BC2C0`).
It pins the five reviewed source drafts and five audits by byte hash, their
exact import graph, all 23 declarations and all 18 intended axiom readouts,
then rejects source code containing a seminorm,
ready-made Holder bound, CMP95/CMP96 consumer, regional `B0`, `TermSource`,
`sorry`, `admit`, or `axiom`.  Its fail-closed self-test is
`tmp/test_step8b24_c6c1_contour_independence.py` (SHA256
`AE01AD8566879533E82A5426C2F2D2580892910C93549831E4F0D354F2FC2183`).
The measured local self-test passed in 0.350 seconds at 21,172,224 bytes peak
RSS.
This remains a static-design result (`compiler_verified = false`).

No source-generic Holder-seminorm consumer should be materialized until the
exact local carrier in CMP95 (1.109) and the public conclusion needed by CMP96
(2.67), including its scale vector and coefficient, have been read from the
primary renders and written next to the proposed signature.  The independent
contour infrastructure above is exempt only because it contains neither that
carrier nor a claimed final Holder bound.  The Fourier route fixes the
mechanism; it does not license guessing the consumer's final scaling.
