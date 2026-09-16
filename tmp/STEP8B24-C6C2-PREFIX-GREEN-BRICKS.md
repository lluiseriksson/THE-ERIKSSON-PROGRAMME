# Step 8b.24 C6c.2: prefix-Green brick boundary

Status: static design only.  No declaration below has been elaborated or
audited.  This note is not evidence for C6c.2 and changes no counter.

## Physical inputs allowed at the public boundary

The C6c.2 producer may take only the data that generate one physical RG
chain:

* dimension and RG block ratio `Lblock : Nat` with their printed positivity
  hypotheses;
* one initial active region and physical background;
* one initial spacing and source coefficient `a`;
* the tracked tower instantiated with its internally named parameter
  `M := Lblock`, so the printed RG factor is definitionally
  `L_source = (Lblock : R)`;
* one closed `Ubar` radius/small-field chain;
* the joint scalar windows already named in the physical regime;
* one terminal Poincare absorption premise
  `cmp99SourcePoincareErrorCoeff d Lblock depth spacing epsilon < 1`.

It may not take a family of `Q_j`, precisions, Greens, coarse covariances,
coercivity constants, inverse laws or recurrence equalities.

The terminal Poincare premise is a **separate upstream reachability
obligation**, not one of the currently certified joint scalar windows.  The
tree proves it at `epsilon = 0` via
`cmp99SourcePoincareErrorCoeff_zero`, which gives the noncontradictory flat
endpoint but only the exactly flat background.  No present theorem produces
the strict inequality at a positive source radius.  Promotion must therefore
keep this premise visible until a named positive-radius producer is proved;
it must not call it a sixteenth freely chosen window or imply that the
existing joint-regime witness discharges it.

The scratch producer now also resolves the only immediate radius coupling:
the nested CMP109 pivot witness has its own `epsilon0`, and the eventual
background cannot use two independent radii.  Taking half the minimum of the
Poincare admissible radius and the existing pivot radius preserves both
CMP109 inequalities by their literal nonnegative linear formulas.  This is a
derived common-radius witness, not a new caller premise.

The later regional large-block parameter `K` (printed `M` in CMP99 Section C)
is deliberately absent from P0--P4.  It first enters the carrier/localization
transport after the RG-scale identity is proved.  Instantiating the tracked
tower parameter by `Lblock` must not restore the rejected diagonal
specialization `K = Lblock`.

## P0 -- canonical truncation of the two physical chains

Define internally generated truncations of
`CMP99SourceActiveRegionChain` and `CMP99SourceUbarRadiusChain` to their first
`r` fine-to-coarse steps.  Both truncations retain the initial fine region,
background, radius and small-field proof; they merely replace the unused tail
by `stop`.

Prove the generalization of the existing terminal bridge:

```text
(generatedRetainedPhysicalTower ...).towerAt r
  = (fullRegionChain.take r).weightedQprimeTower
      ... (fullRadiusChain.take r) ... .
```

The tracked theorem
`cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower`
is exactly the `r = Fin.last depth` endpoint.  P0 must prove the family by
induction; it may not add an equality field to the retained tower or ask the
caller for a truncated chain.

Static re-audit of the tracked tree: the endpoint and its two transport
helpers really are present in
`BalabanCMP99SourceRetainedGeneratedTerminalBridge.lean`, not in the
definition module for `weightedQprimeTower`.  Their exact scopes are:

* `CMP99SourceRetainedPhysicalTower.towerAt_transport` transports selection
  of an already-built retained prefix;
* `CMP99SourceActiveRegionChain.weightedQprimeTower_transport` transports a
  whole generated weighted tower across equality of its active-region index;
* `cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower`
  identifies only the terminal prefix.

There is no tracked arbitrary-`r` theorem and no tracked `take` operation on
either chain.  Thus P0 is a genuine new family bridge, not a re-export of an
existing declaration.  Conversely, its only dependent equality has already
been exercised by the terminal proof, so P0 must reuse those helpers rather
than introduce a new transport axiom or an equality supplied by its caller.

This route avoids a second, much heavier dictionary that rewrites the fine
lattice as `Lblock^r * (Lblock^(depth-r)*N)` and transports active regions
across that arithmetic equality.

### Measured implementation shape

The tracked definitions confirm that both chains expose the fine end first:

* `CMP99SourceActiveRegionChain.step Omega ... tail` stores the current fine
  region at the head and the active coarse region in `tail`;
* `CMP99SourceUbarRadiusChain.step epsilon ... tail` stores the current fine
  radius at the head and `nextFineRadius epsilon` in `tail`;
* the successor branch of
  `cmp99SourceGeneratedRetainedPhysicalTower` installs the identity prefix
  and then maps every successor prefix to `Tail'.towerAt`.

Therefore the truncations should have the following dependent shapes (names
provisional):

```text
CMP99SourceActiveRegionChain.take
  (regions : ... depth) (r : Nat) (hr : r <= depth) : ... r

CMP99SourceUbarRadiusChain.take
  (chain : ... depth epsilon) (r : Nat) (hr : r <= depth) :
    CMP99SourceUbarRadiusChain ... r epsilon
```

At `r=0`, the region truncation is `.stop Omega`, while the radius truncation
is `.stop epsilon chain.epsilon_nonneg`.  At `r+1`, both retain the literal
head constructor and recurse on the tail with
`Nat.le_of_succ_le_succ hr`.  In particular, no caller supplies the terminal
radius or terminal region of a prefix.

Add `takeFin` wrappers using `r.val` and `Nat.lt_succ_iff.mp r.isLt`; all
public prefix theorems should quantify over `r : Fin (depth+1)`, so an
out-of-range truncation proof never appears in their interface.

The exact family theorem should be stated for the generated retained tower:

```text
cmp99SourceGeneratedRetainedPhysicalTower_towerAt_eq_take_weightedQprimeTower
  ... (r : Fin (depth+1)) :
  generated.towerAt r =
    (canonicalRegions.takeFin r).weightedQprimeTower
      ... (chain.takeFin r) fineSmall
```

Its proof is induction on `depth` followed by `Fin.cases` on `r`:

1. the zero-prefix branch is definitional on both sides;
2. the successor-prefix branch unfolds one physical step and applies the
   induction hypothesis to the tail prefix;
3. the only dependent transport is the already measured equality
   `activeCoarseRegion(iteratedLift(depth+1)) = iteratedLift(depth)`.

That transport stays private to the successor proof and should reuse
`CMP99SourceRetainedPhysicalTower.towerAt_transport` and
`CMP99SourceActiveRegionChain.weightedQprimeTower_transport`.  It must not
escape as a caller equality.  The existing terminal theorem should then be a
corollary at `r = Fin.last depth`; retaining it preserves downstream APIs and
provides a regression check on the family theorem.

Static acceptance checks for P0:

1. taking zero steps changes neither the fine region, background, spacing nor
   epsilon;
2. taking all steps is theorem-equal to the original two chains;
3. `take (r+1)` is definitionally headed by the original head constructor;
4. the family theorem contains no supplied truncated chain and no supplied
   equality between towers;
5. no arithmetic reassociation of `regionalLatticeSize` appears in the public
   theorem.

Scratch status (2026-08-17): `tmp/P0CanonicalPrefixTower.lean` now contains
the two internal `take`/`takeFin` definitions, their zero/successor equations,
the private transport package and the complete arbitrary-prefix family proof,
with no placeholder proof.  SHA-256 is
`21028CCBBB4DD660D8F9CBDCC144B37F5CF58E425AA5CD97DD8824A2671BEEFD`.
Together with the P1 scratch target it passes the exact overlay text guard.
It has not been elaborated and therefore is not evidence that dependent
elimination accepts the proposed definitions.  The first P0 elaboration must
stop at its first exact error; no terminal-only fallback is admissible.

## P1 -- retained raw Poincare at every prefix

Construct one `CMP99SourceRetainedPhysicalTower` internally.  For every
source prefix order `j`, apply the existing **chain-generic** theorem
`CMP99SourceActiveRegionChain.norm_sq_le_absorbed_poincare` to the
P0-truncated chains, rewrite its terminal term with
`CMP99SourceActiveRegionChain.terminalFieldNormSq_eq_weightedQprimeTower`,
and transport that `Qprime` through the P0 family bridge.

Do not use
`cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_with_Qprime` directly
at an intermediate prefix.  Its public signature reconstructs a canonical
`iteratedLift Omega j` on `regionalLatticeSize Lblock N j`; an intermediate prefix
of a depth-`k` fine tower instead retains the original fine lattice and
region.  The chain-generic theorem is precisely the tracked endpoint that
avoids the otherwise necessary factorization/transport dictionary.
The resulting raw estimate on the original fine carrier is

```text
(1 - B_j) * ||phi||^2
  <= A_j * energy_A(phi) + C_j * ||Q_j(A) phi||^2.
```

Here `A_j`, `B_j` and `C_j` must be the explicit coefficients already used
by `cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_with_Qprime` at that
prefix.  The depth-zero retained prefix is an algebraic identity endpoint:
`A_0 = B_0 = 0`, `C_0 = 1` and `Q_0 = I`.  P1 may expose its raw estimate,
but it must not claim `A_0 > 0` and it is **not** CMP85 source `j=1`.

For every physical prefix `j >= 1`, P1 must prove `A_j>0`, `C_j>0` and
`B_j<1` from the same chain and the one terminal Poincare premise named at
the public boundary.  None of the prefix-indexed facts may be a caller
field.  P2 consumes only this positive-index package.

The prefix smallness need not become a new family-valued window.  The tracked
recursions have nonnegative coefficients and errors, so P1 should first prove
the missing monotonicity lemmas

```text
r <= k -> EnergyCoeff r spacing epsilon <= EnergyCoeff k spacing epsilon
r <= k -> ErrorCoeff  r spacing epsilon <= ErrorCoeff  k spacing epsilon.
```

The proof must be by **adjacent depth**, followed by transitivity.  After
unfolding depths `n+1` and `n+2`, both sides use the *same* transformed
arguments `Lblock*spacing` and `nextFineRadius epsilon`.  The energy comparison
therefore uses only the adjacent-depth induction hypothesis under the
nonnegative multiplier `2 * blockAverageWeight`.  The error comparison uses
that energy comparison under the nonnegative `scaledGradientStepError`, plus
the adjacent error comparison under the nonnegative block-average weight.
The zero-depth branches follow from the existing coefficient nonnegativity.

In particular, this proof does **not** require, and P1 must not add, any
monotonicity theorem for `nextFineRadius` or any comparison between `epsilon`
and `nextFineRadius epsilon`.  Such a comparison would introduce an irrelevant
domain/smallness obligation into a purely structural depth theorem.
Consequently the single terminal hypothesis
`ErrorCoeff k spacing epsilon < 1` implies every prefix hypothesis by
transitivity.  If this monotonicity fails to elaborate in the exact recursive
normal form, P1 stops there: accepting `forall r, ErrorCoeff r < 1` from the
caller would add a new scalar family and is not an admissible fallback.

Acceptance gates:

1. The `Q_j` in the conclusion is definitionally or theorem-equal to the
   retained `towerAt j` prefix.
2. The field `phi` lives on the original fine carrier, not on the terminal
   coarse carrier.
3. The equality between scaled gradient energy and the literal covariant
   Laplacian quadratic form is cited by name.
4. The raw theorem may include the depth-zero identity endpoint, but the
   first physical package is explicitly the positive prefix `j=1`; an
   empty-prefix convention is not silently substituted for source `j=1`.
5. No equality of the form `regionalLatticeSize depth = Lblock^j * ...` is needed
   at the public boundary; all dependent transport is confined to P0.
6. Prefix `B_j < 1` is derived from the one terminal `hsmall` by the named
   monotonicity theorem; it is not a new input.

Scratch status (2026-08-17): `tmp/P1CoefficientMonotonicity.lean` contains
adjacent/full monotonicity for both scalar ledgers and the three exact
consumers needed downstream: positive `A_j` for `j>0`, positive `C_j`, and
prefix `B_j<1` from one terminal budget.  It now also contains the complete
absorbed prefix-Poincare consumer on the original fine carrier.  That theorem
fixes `matrixSUNAdjointModel Nc` internally: `terminalFieldNormSq` is generated
with that physical model, so quantifying over an arbitrary `rho` would require
a nonexistent equality between two retained towers.  SHA-256 is
`BF0724FAF5967A7A2A909A0919597FA21C81A96123832E1430E1A908A20A0382`.
It is text-guarded but not elaborated; none of these declarations is counted
or promoted yet.

The future P0/P1 audit surface is now explicit rather than inferred from the
sources.  `tmp/P0CanonicalPrefixTowerAudit.lean` (SHA-256
`E0CA421071FB337436D8B247C9DEF91708A0198D54A081A1A23341E4A9466307`)
contains ten readouts and `tmp/P1CoefficientMonotonicityAudit.lean` (SHA-256
`890EFBDCAE9CB45C05CA8CBBBC35B3DD5FBBE1EE5A6F27458FF620C1BCED5A19`)
contains eight.  Their exact four-file scope is pinned by
`tmp/STEP8B24-C6C2-P0-P1-PATHS.txt` (SHA-256
`9663174609EA023FCC366661E68AB3E50E3A3934D64E0F3E804249AD97106001`).
The repository text gate reports `LEAN_OVERLAY_TEXT_OK files=4`, and the
static declaration/readout count is `18/18`.  These checks do not elaborate
either dependent proof and therefore leave both bricks `NOT CHECKED`.
The fail-closed scope/hash/import/readout gate is
`tmp/audit_step8b24_c6c2_p0_p1_static.py` (SHA-256
`EB8DB5D6B842785A52ADFC9BB298EFD6E4F461BDD6285A75A1AE119875B518EB`);
its literal result is
`STEP8B24_C6C2_P0_P1_STATIC_OK files=4 bricks=2 declarations=18
axiom_readouts=18 compiler_verified=false counters=20/41 term_source=0`.

## P2 -- source-`a_j` prefix Green, effective precision and literal `C^(j)`

For source `j>=1`, first define the fine-carrier quantities.  Write `s0` for
the fine spacing and `sj` for the exact terminal spacing of prefix `j`:

```text
aSource(j) = cmp99SourceMassParameter a (Lblock : R) (j-1)
sj           = (T.towerAt j).terminalSpacing
bWeighted_j  = aSource(j) * sj^(-2)
volumeRatio_j = sj^d / s0^d
bCount_j     = bWeighted_j * volumeRatio_j
             = aSource(j) * sj^(d-2) / s0^d
QdagSource_j = volumeRatio_j * Q_j(A).adjoint
DeltaBare(m) = -Delta_A + m^2 * I
K_j(m)       = DeltaBare(m) + bWeighted_j * QdagSource_j Q_j(A)
             = DeltaBare(m) + bCount_j * Q_j(A).adjoint Q_j(A).
```

This distinction is forced by the primary formula and the tracked adjoint
dictionary.  CMP85 (2.20), visually checked on printed p. 610, uses
`a_j (L^j epsilon)^(-2) Q_j^* Q_j`, where `Q_j^*` is the adjoint for the two
lattice-spacing scalar products.  The tracked theorem
`CMP99SourceWeightedRegionalTower.adjoint_eq_spacingRatio_smul_weightedAdjoint`
instead says

```text
Q_j.adjoint = (s0^d / sj^d) * QdagSource_j.
```

Consequently the coefficient multiplying Lean's counting-Hilbert adjoint is
`bCount_j`, not `bWeighted_j`.  This is the same volume normalization encoded
by `cmp99SourceCountingStratumWeight`, but with the CMP85 source shift kept
explicit: prefix `j` uses `aSource(j)=a_(j)` in CMP85 notation and terminal
spacing `sj`, whereas the tracked stratified index starts at zero.  Reusing
`cmp99SourceCountingStratumWeight ... (j-1)` would therefore put the wrong
spacing power on the coefficient.

There are two independent source scalars here.  `m` is the bare physical
mass in CMP85 (2.17), (2.20) and (2.22); `aSource(j)` is the flowing
averaging coefficient `a_j`.  The tracked identifier
`cmp99SourceMassParameter` names the latter for historical reasons and must
not be substituted for `m`.  Conversely,
`cmp99SourceGeneratedPhysicalMass` is the normalized coefficient of the
tracked `Q'^*Q'` term and is not the bare `m^2` summand either.

The generic CMP85 package keeps `m` explicit.  The hRpoly physical
specialization fixes `m := 0` internally, exactly as the already sealed
`physicalPrecision_complexification_eq_fullComplexAction` theorem does.  It
must prove that specialization rather than silently dropping the scalar
summand.  This is consistent with the separately sealed mass-zero CMP89
nonvanishing route; the conditional massive-symbol window remains a distinct
source dictionary and is not discharged by `a_j`.

The existing `cmp99SourceGeneratedPhysicalPrecision` is only a proof
template: it normalizes the absorbed estimate and therefore installs
`C_j/A_j` as the coefficient of `Q'^*Q'`.  P2 instead needs one small generic
algebra lemma that keeps the independently generated averaging coefficient
`b_j` visible.  From

```text
(1-B_j) * ||phi||^2 <= A_j * energy(phi) + C_j * ||Q_j phi||^2
```

with `A_j>0`, `C_j>0`, `B_j<1` and `bCount_j>0`, derive coercivity of
the counting representation
`DeltaBare(m) + bCount_j Q_j.adjoint Q_j` with the literal floor

```text
(1-B_j) * min(A_j^(-1), bCount_j * C_j^(-1)).
```

The proof multiplies the absorbed inequality by the displayed minimum and
uses its two projections separately.  It must then prove the displayed
operator equal to the source-weighted form using the exact adjoint theorem;
neither `bWeighted_j` nor `bCount_j` may be silently substituted for the
other.  Positivity comes from the tracked `cmp99SourceMassParameter_pos`
theorem and the exact positive fine/terminal spacing laws.

Derive internally

```text
coercivity_j = (1-B_j) * min(A_j^(-1), bCount_j * C_j^(-1)) > 0
```

and prove `IsCoerciveCLM K_j coercivity_j`.  Construct `G_j` from this theorem and
prove both inverse laws.

The next two operators must follow the literal CMP85 formulas, not the
existing conditional/coarse-covariance middle.  CMP85 (2.21) and (2.30) give

```text
DeltaEff_j = bWeighted_j * I
  - bWeighted_j^2 * Q_j(A) G_j QdagSource_j,
cStepWeighted_j = a * spacing_(j+1)^(-2),
CPrecision_j = DeltaEff_j
  + cStepWeighted_j * QdaggerSource_step(A_j) Q_step(A_j),
C^(j) = CPrecision_j^(-1).
```

As in (2.20), the counting-Hilbert presentation has a distinct coefficient:

```text
cStepCount_j = cStepWeighted_j
  * spacing_(j+1)^d / spacing_j^d,
CPrecision_j = DeltaEff_j
  + cStepCount_j * Q_step(A_j).adjoint Q_step(A_j).
```

The exact one-step weighted-adjoint dictionary must prove equality of these
two operator presentations.  Equating `cStepWeighted_j` and `cStepCount_j`
would repeat the mass-versus-counting normalization bug and is rejected.

Here the projector `P(A)` printed in (2.30) is the **one-step** projector
`Q_step(A_j)^dagger Q_step(A_j)` on the scale-`j` carrier.  It is not the
fine-carrier prefix projector `Q_j(A)^dagger Q_j(A)`.

This is a measured non-identification.  The tracked
`cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle` is
`Q_j G_j^2 Q_j^dagger`; it is the conditional-covariance middle used by the
gauge projection and is **not** the printed `CPrecision_j`.  No theorem in the
tracked tree presently identifies the two, and P2 must not reuse that inverse
under a source-facing name.

Split the construction into three explicit bricks:

* **P2a:** source-`a_j` fine precision `K_j`, its coercivity and `G_j`;
* **P2b:** for source `j >= 1`, the literal effective quadratic operator
  `DeltaEff_j` of (2.21),
  including its symmetry and nonnegative quadratic form obtained from the
  completed-square/Schur identity for `K_j`;
* **P2c:** for source `j >= 1`, the literal coarse precision of (2.30), its
  internally proved injectivity, and the constructed inverse `C^(j)` with
  both inverse laws.

The source-zero object is deliberately excluded from P2b/P2c.  CMP85 (2.17)
defines `Delta^(0) = -Delta_A + m^2` separately, before the Schur formula
(2.21).  Consequently `C^(0)` is constructed in P4a from (2.17)+(2.30), not
by evaluating the positive-level Schur package at a fictitious `G_0`.

For the recurrence brick, existence of `C^(j)` only needs internally proved
injectivity.  Finite dimensionality then constructs a linear equivalence and
its continuous inverse, exactly as the existing coercive-covariance module
constructs an inverse after injectivity.  This route does not invent an
unnamed coercivity constant.  Quantitative bounds for `C^(j)` are a separate
analytic output and may not be smuggled into P2 as an assumed norm bound.  A
viable proof of injectivity is the block quadratic form

```text
<phi, Delta_A phi>
  + b_j * ||Q_j phi - eta||^2
  + cStepCount_j * ||Q_step eta||^2,
```

together with the already generated prefix Poincare control for
`Q_(j+1) = Q_step Q_j`.  Thus no caller-supplied positivity of
`CPrecision_j` is required.

Concretely, for `eta` in the kernel of `CPrecision_j`, set
`phi = b_j * G_j (Q_j^dagger eta)`.  The completed-square identity gives
nonnegative terms whose sum is zero, hence `Q_j phi = eta`, zero covariant
energy and `Q_step eta = 0`.  The prefix-`j+1` Poincare theorem forces
`phi=0`, and therefore `eta=0`.  This is the sole injectivity argument; a
caller-provided `CPrecision_j` inverse or positive lower bound is rejected.

The exact finite-dimensional inverse construction is already supported by
the pattern in `CoerciveCovariance.lean`, but P2c must use only the proved
injectivity, not manufacture a coercivity constant.  For the literal
endomorphism `CPrecision_j : E ->L[R] E`, define internally

```text
Eequiv =
  (CPrecision_j.toLinearMap.linearEquivOfInjective
    CPrecision_j_injective rfl).toContinuousLinearEquiv
C^(j) = Eequiv.symm.toContinuousLinearMap.
```

The two public inverse laws are then `symm_apply_apply` and
`apply_symm_apply`, lifted extensionally to continuous-linear-map
composition.  The physical public constructor exposes neither
`CPrecision_j_injective` nor `Eequiv` as an input.  If the inverse-from-
injective pattern is factored into a generic helper, that helper may accept
injectivity; the source-facing P2c theorem must prove and supply it
internally.

The kernel proof must remain split into named phases so that no positivity is
lost inside automation:

1. pair `CPrecision_j eta = 0` with `eta`;
2. rewrite by the P2b completed-square identity into three nonnegative
   summands;
3. prove separately that the energy term, mismatch square and one-step
   projector square vanish;
4. derive `Q_j phi = eta` and `Q_step eta = 0`;
5. rewrite `Q_(j+1) phi = Q_step (Q_j phi) = 0` by the P0 tower recursion;
6. apply the raw P1 prefix-`j+1` Poincare inequality to force `phi=0`, then
   `eta=0`.

This phase order is semantic: replacing steps 2--6 by a supplied positive
lower bound would rename the missing proof.

Acceptance gates:

1. The flowing coefficient is `cmp99SourceMassParameter ... (j-1)`, never
   `cmp99SourceGeneratedPhysicalMass` and never the complete stratified sum.
   Its printed coefficient `bWeighted_j` and counting coefficient `bCount_j`
   are both named and related by the exact volume ratio.
2. The source weighted adjoint is connected to the counting-Hilbert adjoint
   by the exact spacing theorem before it appears in a printed formula; P2a
   proves equality of the two operator presentations rather than identifying
   their scalar coefficients.
3. `C^(j)` is constructed from the literal precision in CMP85 (2.30), not
   from `Q_j G_j^2 Q_j^dagger`, and it is not a supplied inverse.
4. Every object is a projection of one internally generated prefix package.
5. The coercivity constant exposes both inverse branches `A_j^(-1)` and
   `bCount_j*C_j^(-1)`; replacing it by an unnamed positive witness is
   rejected.
6. The source equations used here are recorded distinctly: (2.20) defines
   `G_j`, (2.21) defines `DeltaEff_j`, and (2.30) defines `C^(j)`.  A green
   theorem about the conditional middle does not satisfy any of these gates.
7. The two projectors are type-separated: the prefix projector belongs to
   `K_j` on the fine carrier; the one-step projector belongs to
   `CPrecision_j` on the scale-`j` carrier.

Scratch status (2026-08-17):
`tmp/P2SourceCoefficientCoercivity.lean` contains only the admissible generic
two-weight absorption lemma, its bare-mass-preserving operator form, plus the scratch-only
positive-prefix coefficient dictionary and the proposed exact equality
between the source-weighted and counting-Hilbert operator presentations.  Its
coefficient recurrence fixes `L_source := (M : R)` from the tower parameter;
there is no second real block ratio in the scratch API.  Its
generic absorption coefficient is
literally
`(1-B) * min A⁻¹ (b*C⁻¹)`; neither branch is hidden in a positive witness.
The algebraic absorption and strict positivity are separate declarations, so
`B<1` is consumed exactly by the latter and is not a dead premise.
The scratch file now also contains the proposed source-facing positive-prefix
precision and coercivity producer.  It constructs the one retained tower
internally, fixes the matrix adjoint model and derives every prefix budget
from the one terminal `hsmall`; neither `T`, `Q_j`, the coefficient nor a
coercivity witness is a public input.  The independent bare mass remains
literal and needs no sign hypothesis because only `mass^2` enters.  The Green
operator, positivity of the robust floor and both ordered inverse laws are now
also present as proposed scratch declarations, all constructed from the same
coercivity theorem.  Symmetry of the bare-mass precision, generated prefix
precision and constructed Green is now derived internally as well; no `hG`
is exposed by the source-facing layer.  Thus P2a is source-complete at the scratch-text level but
is not a verified brick.  None of the new physical declarations has been elaborated; in
particular the dependent prefix, division normalization and final `simpa`
are only candidates until the first stop-on-error focal.
SHA-256 is
`47A6DA2EE8BC704A3ECFBFA28017AEC0E2137328956417F18E4857180F00F4C0`.
P0--P2 scratch files pass the exact text guard but remain unelaborated.

P2b now also has a scratch-only candidate in
`tmp/P2bEffectiveQuadratic.lean`.  It fixes the counting-Hilbert form of
(2.21) as

```text
bWeighted * I - (bWeighted * bCount) * Q * G * Q.adjoint,
```

constructs `phi = bCount * G * Q.adjoint eta` internally, derives its Euler
equation from the right-inverse law for the P2a precision, and proves the
exact completed-square identity, nonnegativity and symmetry.  The generated
source specialization constructs its Green and both coefficient conventions
from P2a, and discharges the generic Green-symmetry premise internally.  It does not accept a
fine field, Euler equation or completed-square equality from the caller.
The mixed coefficient is deliberate: converting the printed weighted
adjoint to the counting adjoint changes only one of the two printed
`bWeighted` factors.  The file passes the exact text guard but has not been
elaborated and therefore is not a verified brick or a counter movement.
SHA-256 is
`C4CD860BA0B83EE09505DAC966F982DC0ED4A7F216EEEB339B5D00E5C98EB71D`.

The generic P2c boundary is now written in
`tmp/P2cCoarseCovariance.lean`.  It defines the literal one-step precision,
proves that its quadratic form is the P2b completed square plus the
`cStepCount * ||Qstep eta||^2` term, eliminates its kernel in the mandated phase
order, and constructs the finite-dimensional inverse with both composition
laws.  The generic kernel helper accepts only the zero-control implication

```text
energy(phi) = 0 -> Qstep (Q phi) = 0 -> phi = 0.
```

This is not a source-facing hypothesis.  The scratch file now derives it
internally from the exact P0 recursion, the raw P1 prefix-`j+1` Poincare
inequality, and the nonnegative bare-mass energy identity; the derivation has
not yet been elaborated.  The physical scratch producer now also constructs
the printed `cStepWeighted`, its counting coefficient `cStepCount`, and their
exact weighted-adjoint operator equality.
The scratch boundary now constructs the one-step weighted adjoint from the
exact factor `M^d` and states the defining lattice-spacing pairing separately;
the operator-term equality is therefore not accepted as a tautological
rescaling without its semantic pairing law.  Finally, the source-facing
package defines the positive step index, constructs the literal (2.30)
precision, proves its complete weighted-source presentation, derives
injectivity internally, constructs `C^(j)`, and exposes both inverse laws.
Thus P2c is source-complete at the scratch-text level but remains wholly
unelaborated and unverified.  The file passes the exact text
guard; SHA-256 is
`9C552B1F3F21B1253DAF8DDE15B36BBE09DDFBA18536D6EC4C166B3EBE4CC5E6`.

P0--P2c now have one exact static audit boundary.  The ordered ten-file scope
(five source/audit pairs) is
`tmp/STEP8B24-C6C2-P0-P2-PATHS.txt` (SHA-256
`E1B145A10E9174FAF6915FF920551CA7633CCA38F875D96A9AE7294F49BEE15F`).
It includes 78 public declarations and exactly 78 sibling axiom readouts.
`tmp/audit_step8b24_c6c2_p0_p2_static.py` (SHA-256
`DB18E3C2C353184AB540358E124FCE7296031853CC7AC961552CBCF60A9CF234`)
pins every blob and import edge and reports
`STEP8B24_C6C2_P0_P2_STATIC_OK files=10 bricks=5 declarations=78
axiom_readouts=78 compiler_verified=false counters=20/41 term_source=0`.
The repository overlay text gate also passes on the exact ten paths.  This
unifies audit coverage only; it is not elaboration evidence for any P0--P2c
declaration.

## P3 -- exact one-step recurrences (2.41) and (2.42)

Introduce the scalar abbreviations

```text
b_j     = bWeighted_j = a_j * spacing_j^(-2),
c_j     = a * spacing_(j+1)^(-2),
b_(j+1) = b_j * c_j / (b_j + c_j).
```

P3 is written in the source-weighted orientation, with `QdagSource`; these
are not the counting coefficients used by the P2a coercivity proof.  The P2a
operator-presentation equality is the mandatory bridge between the two
orientations and is cited before inverse uniqueness is used.

The last equality must be derived from the exact source recurrence specialized
to `L_source = (Lblock : R)` and the tower theorem instantiated at
`M := Lblock`, namely
`spacing_(j+1) = (Lblock : R) * spacing_j`; it is not a new parameter law or
a caller-supplied equality between independent scales.
With these scalars, prove one generic three-space block-Gaussian lemma for
`Q_j : H -> K` and `Q_step : K -> L`, using the exact source coisometries.
Its physical specialization first proves the averaged identity in the exact
source orientation:

```text
Q_(j+1) G_(j+1)
  = (a * a_j / a_(j+1)) * spacing_j^(-2)
      * Q_step(A_j) * C^(j) * Q_j(A) * G_j.          (2.41)
```

Then prove the fine-carrier Green recurrence:

```text
G_(j+1)
  = G_j
    + a_j^2 * spacing_j^(-4)
        * G_j * Q_j(A)^* * C^(j) * Q_j(A) * G_j.    (2.42)
```

The proof may use that generic inverse/resolvent lemma, but the physical
specialization must prove its premises from:

* the exact `Q_(j+1) = Q_step(A_j) Q_j` recursion;
* the exact `a_j` recurrence;
* both inverse laws of `G_j`, `G_(j+1)` and `C^(j)`;
* the source-weighted adjoint dictionary;
* the exact fine/block spacing relation.

The algebraic engine is the Schur complement with the literal
`DeltaEff_j + c_j Q_step^dagger Q_step`.  It must show directly that the RHS
of (2.42) is both a left and right inverse of
`Delta_A + b_(j+1) Q_(j+1)^dagger Q_(j+1)` and then use inverse uniqueness.
This prevents defining `G_(j+1)` by the desired RHS.  Eq. (2.41) follows from
the same inverse laws plus `b_j + c_j =
(a * a_j / a_(j+1)) * spacing_j^(-2)`.

### Exact generic algebra contract

The generic lemma should expose three Hilbert spaces and typed arrows

```text
Q  : H -> K,       Qdag : K -> H,
R  : K -> L,       Rdag : L -> K,
P  = Rdag R,
S  = Q G Qdag,
K_b    = A + b Qdag Q,
K_beta = A + beta Qdag P Q,
D      = b I - b^2 S,
CPrec  = D + c P.
```

It receives only the two-sided inverse laws for `(K_b,G)`,
`(K_beta,Gnext)` and `(CPrec,C)`, the one-step coisometry
`R Rdag = I`, and the scalar identity `beta * (b+c) = b*c`.  It does **not**
receive either source recurrence as an equality of operators.  Define the
candidate

```text
Hcandidate = G + b^2 G Qdag C Q G.
```

The right-inverse calculation reduces to

```text
b^2 C + (beta P - b I)
  + b^2 (beta P - b I) S C = 0,
```

using `CPrec C = I`, `P^2=P` and `beta(b+c)=bc`.  The left-inverse
calculation is the order-reversed identity

```text
(beta P - b I) + b^2 C
  + b^2 C S (beta P - b I) = 0,
```

using `C CPrec = I`.  Hence inverse uniqueness gives
`Gnext = Hcandidate`, which is (2.42).

After this identification, applying `R Q` and using

```text
I + b^2 S C = b C + c P C,
R P = R
```

gives `R Q Gnext = (b+c) R C Q G`, the exact (2.41) orientation.  This
derivation also fixes which inverse law of `C` is used on each side and keeps
the rectangular compositions type-correct.

Neither displayed equality may be an input.  Eq. (2.41) is an independent
normalization/orientation gate for (2.42), not merely a docstring.

Scratch status (2026-08-17): `tmp/P3ScalarRecurrence.lean` now fixes the
three printed weighted coefficients directly from
`cmp99SourceMassParameter` and the exact next spacing `L*spacingJ`.  It
states positivity, derives `beta*(b+c)=b*c`, derives the independent (2.41)
normalization `b+c=(a*a_j/a_(j+1))*spacingJ^(-2)`, and keeps the (2.42)
coefficient visibly equal to `a_j^2*spacingJ^(-4)`.  These are candidate
proofs using the source recurrence, not caller laws.  The file passes the
text guard but is unelaborated.  The companion scratch file
`tmp/P3BlockGaussianAlgebra.lean` now records both orderings of the Schur
bracket as noncommutative polynomial certificates.  Each certificate uses
exactly one inverse residual, the explicit projector residual `P^2-P`, and
the image of `beta*(b+c)-b*c`; scalar centrality is supplied only by the
`Algebra ℝ` structure.  It neither accepts `Gnext` nor either printed
recurrence as an operator equality.  This is still scratch text: it has not
been elaborated, and the typed three-space lift plus physical specialization
remain open.  The scalar file SHA-256 is
`C6BF25BF5865A8D8C65488CF65BA69D4BA64507F342D04DAC7C1E98E07723741`.
The noncommutative certificate SHA-256 is
`9205E8F1154AE75672E38F633FE4BBAA400DA231497BDBD405204810A558AF76`.
`tmp/P3TypedSchurBrackets.lean` now supplies the first typed lift: it defines
the source-oriented projector `Rdag R`, the sandwich `Q G Qdag`, and the
literal Schur precision on the intermediate space; derives projector
idempotence from the exact coisometry `R Rdag = I`; and specializes both
noncommutative certificates without replacing either source-weighted adjoint
by Lean's counting adjoint.  Its SHA-256 is
`ADAE3444F77E0132A13B2E51B49C48357082CA01527394EAB46A7770E9F261E4`.
The same file also derives `R P = R` from that coisometry and extracts the
exact typed averaging identity
`R (I + b^2 S C) = (b+c) R C` from the right Schur inverse.  Thus the
orientation and the coefficient consumed by (2.41) are explicit before its
source normalization is substituted.  The file passes the text and
delimiter guards but is unelaborated; it supplies only the intermediate-space
boundary consumed by the separate outer calculation below.
`tmp/P3TypedGreenInverse.lean` now writes the outer calculation itself.  It
defines the fine and next precisions and the (2.42) candidate; decomposes the
next precision as the fine precision plus the literal error
`Qdag (beta P-b I) Q`; proves the candidate right and left inverse laws from
the corresponding fine/Schur laws; identifies an independently supplied
`Gnext` only afterward by inverse uniqueness; and derives the typed (2.41)
orientation with coefficient `b+c`.  The source formula for that coefficient
is still substituted only by `P3ScalarRecurrence`, not assumed here.  The
file passes text and delimiter guards and has SHA-256
`B1F8836FD77501231159FE69C416D397B73FA8A9A4A8BB62931AF7B6959FB6EB`.
It is unelaborated scratch, so none of these declarations is compiler
evidence or counted.  The physical tower specialization remains open.

Static inspection of that specialization exposed one mandatory dictionary:
the retained tower stores `nextAverage` but not its weighted coisometry as a
field.  `tmp/P3SourceStepCoisometry.lean` therefore derives, rather than
assumes, the adjacent weighted-adjoint factorization

```text
W_(j+1) = W_j (M^d * nextAverage.adjoint)
```

from `Q_(j+1)=nextAverage Q_j`, the two exact prefix weighted-adjoint
relations, and the terminal/fine volume ratios.  It then derives the literal
one-step coisometry from the two prefix coisometries.  This is the exact
normalization premise required by typed P3 and prevents replacing it by the
stored norm inequality.  The file passes text and delimiter guards and has
SHA-256
`742F5845485CD7EF31CBA4A7903450DC0FE7A024791DA3DE90857B6799500762`.
It remains unelaborated scratch and is not counted.

`tmp/P3PhysicalScalarSpecialization.lean` fixes the remaining physical
index shift before any operator rewriting: a positive step of value `k`
uses recurrence index `k-1` for the current `b`, literal next-prefix spacing
for `c`, and recurrence index `k` for `beta`.  It proves three separate
equalities to the current, step, and next source-weighted coefficients.  Its
SHA-256 is
`E7F0FBF462B2A1F820B85B17D6F02F8A5BF61FB6361F384AEDECB50E10FFB83A`.
It passes text and delimiter guards but remains unelaborated and uncounted.

`tmp/P3PhysicalOperatorDictionary.lean` now writes the three operator
identifications required before invoking the generic recurrence: typed fine
precision equals generated P2a, typed Schur precision equals generated P2c,
and typed next precision equals generated P2a at the next positive prefix.
The last equality explicitly composes the `Q'` recursion, adjacent
weighted-adjoint factorization, and `beta` index shift; it does not accept a
next-precision equation.  Its SHA-256 is
`8ADB657A03E911E04A9551FC38B42393722D842C4E3D7CCB1B53EC4C62D44BCC`.
It passes text and delimiter guards but remains unelaborated scratch and is
not counted.  The remaining P3 source theorem must now assemble the already
generated inverse laws and substitute the two printed scalar normalizations.

`tmp/P3PhysicalGreenRecurrence.lean` now writes that final assembly.  One
source-generated theorem constructs the fine, next and Schur inverse laws
from P2a/P2c, proves the literal one-step coisometry, derives the scalar
recurrence at the *current terminal spacing*, and returns the typed (2.42)
and (2.41) equalities together.  Two corollaries then expose exactly the
printed coefficients `a_j^2 spacing_j^(-4)` and
`(a a_j/a_(j+1)) spacing_j^(-2)`.  No family of Green operators or either
recurrence is accepted from the caller.  Its SHA-256 is
`09D724231FA75DB8500369DA91A83751AA36FB64E96549CACEF38E6B7B317ECF`.
The file passes text and delimiter guards.  P3 is therefore source-complete
at the scratch-text level, but every file in the chain remains unelaborated;
none is compiler evidence or counted.
`tmp/P3PhysicalGreenRecurrenceAudit.lean` is now the exact three-readout
sibling of the physical endpoint, SHA-256
`1FC0EBD7D954208DC6F93885BBD9ACF6093671B3064D2D8726882BEE3E34D8CE`.
The separate `tmp/P3PhysicalGreenRecurrenceAggregateAudit.lean` fixes the
18-readout chain gate covering the scalar recurrence, both abstract and typed
brackets, both candidate inverse laws, inverse uniqueness, averaged
recurrence, step coisometry, all three physical dictionaries and both printed
endpoints.  Its SHA-256 is
`2DFFE3FFCC2CFEAF3E7AFBCAFC66BAFF888AC0FC84FBD221B3ED29DECF644301`.
The complete fifteen-file P0--P3 dependency closure is frozen in
`tmp/P0-P3-SCRATCH-MANIFEST.sha256`; the local byte gate reports `15/15`
matches.  Manifest SHA-256:
`A7D239AF4AD0CF7FF18E3BD1D4272E33857D5BA5E6F8E7F0BAE986E9DD8C8E90`.

## P4a -- physical base `G_1 = C^(0)`

The primary CMP85 render fixes this as a separate identity immediately
before (2.43):

```text
G_1 = C^(0),eta
```

This is not a chosen initial covariance.  At source index one,
`a_1 = a`, `Q_1 = Q_step`, and (2.17), (2.20), (2.21), (2.30) reduce both
inverse constructions to the same literal precision

```text
-Delta_A + m^2 + a * spacing_1^(-2) * Q_step^dagger * Q_step.
```

In Lean's coefficient convention this uses
`cmp99SourceMassParameter a (Lblock : R) 0 = a`.  P4a constructs the literal
base precision from (2.17)+(2.30), proves it equal to the P2a precision of
`G_1` from the generated prefix dictionaries, constructs `C^(0)` internally,
and obtains the Green/covariance equality from the two ordered inverse laws.
It may not accept `G_1 = C^(0)`, a base covariance, or a precision equality
from the caller.  In particular it may not invoke P2b/P2c at index zero.

Acceptance gates:

1. The public theorem states the operator equality `G_1 = C^(0)` on the
   common generated fine carrier.
2. The proof cites the literal source base coefficient and one-step average;
   it does not use `cmp99SourceGeneratedPhysicalMass`.
3. The generic theorem retains the bare `m^2 * I` summand.  Its hRpoly
   specialization fixes `m := 0` internally and cites the sealed mass-zero
   physical-precision dictionary; it does not identify `m` with `a_1`,
   `b_1`, or `cmp99SourceGeneratedPhysicalMass`.
4. `G_1` is generated by P2a; `C^(0)` is generated separately from the
   (2.17)+(2.30) base precision.  Their precision equality is proved before
   inverse uniqueness is applied.
5. The theorem is separately audited; it is not hidden as a simplification
   inside the finite-sum induction.

Scratch status (2026-08-17): `tmp/P4aPhysicalBase.lean` now writes the
source-complete candidate.  It constructs the literal first step and prefix;
derives `Q_1=R`, `W_1=Rdag`, and `a_1=a`; defines the base precision with the
independent bare-mass term retained; proves it equal to generated P2a only
after those dictionaries; transports coercivity; constructs `C^(0)` as a
new inverse; proves both ordered inverse laws; and obtains `G_1=C^(0)` by
right-inverse uniqueness.  P2c is never invoked at index zero.  Source file
SHA-256:
`DB0DCD721E7A62CB6DC42320876A70DB2B34895C157206626C0437C5A2937923`.
The twelve-declaration audit SHA-256 is
`40EF18405998C5A6C8DB4B6EF95F1C0290355666720F9F8B42FBEAFBAC69C67B`.
Both pass text and delimiter guards but remain unelaborated scratch; P4a is
not compiler evidence or counted.

## P4b -- finite induction (2.43)/(CMP89 (2.34))

Iterate P3 over `Finset.Ico 1 k`, starting from the P4a identity, and
obtain

```text
G_k = C^(0),eta
  + sum j in Ico 1 k,
      a_j^2 * spacing_j^(-4)
        * G_j * Q_j^* * C^(j) * Q_j * G_j.
```

Acceptance gates:

1. `Ico 1 k` is proved to encode precisely `1<=j<k`.
2. The source coefficient index is shifted (`j-1`) independently of the
   operator prefix index (`j`).
3. The base `k=1` theorem cites the separately audited P4a
   `G_1=C^(0)` equality.
4. The induction step uses P3 and finite-sum insertion only; it does not use
   the regional `Omega` telescope.
5. The result is an operator equality on one named fine carrier.

Scratch status (2026-08-17): `tmp/P4bFiniteTelescoping.lean` now contains
the additive `Finset.Ico` telescope and a named literal physical increment
whose coefficient and operator order are inherited definitionally from the
P3 `(2.42)` producer.  The one-step physical theorem cites P3 directly; it
does not accept the recurrence as a caller hypothesis.  Source SHA-256:
`E6BFBDC40E841339A330750CCE4A24641F5F37F24CAB54EB4B42A3D1844A9527`.
The fourteen-declaration audit SHA-256 is
`4C4873753E67C8893FB5BA5E6409AD387D08C0039D73FEB74D138CB512350472`.
Both pass the text guard but remain unelaborated scratch.  The dependent
natural-index adapter and substitution of the separately generated P4a base
are now written, with the recurrence required only on `1 ≤ j < depth`.
The final equivalence reindexes that interval bijectively to
`ScratchCMP85PositiveCoarseStep depth`, and the candidate public endpoint
states the complete source sum (2.43) on one fine carrier.  P4b is still not
compiler evidence or counted.

## P5 -- carrier/spacing transport to CMP89/CMP95 notation

Only after P4b, transport the operator identity through the canonical lattice
and spacing equivalences consumed by CMP95/CMP96.  P5 may rewrite types and
the printed scale notation; it may not change the family of operators, erase
`Q_j^*`, or absorb `a_j^2*spacing_j^(-4)` into an opaque constant.

P5 is also the first stage permitted to introduce the independent regional
large-block parameter `K`.  Its scale theorem must retain simultaneously
`Lblock^(j)` for the RG spacing and `K*Lblock^(j)` for the regional carrier;
it may not collapse them to one natural parameter.

Scratch status (2026-08-17):
`tmp/P5PhysicalGreenScaleDictionary.lean` specializes the P4 chain to the
literal full coarse region `2*(K*Q)`, tower depth `depth+1`, `M := Lblock`,
and bare mass zero.  It then reindexes the complete P4b operator identity
through the existing
`cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv`; no carrier equality,
Green family, recurrence or final sum is a caller premise.  The public
`...eq234_literal` endpoint additionally expands the named increment in its
conclusion, so the exact `a_j^2*spacing_j^(-4)` coefficient and
`G_j Q_j^dagger C^(j) Q_j G_j` order are visible rather than recoverable only
by unfolding.  The tracked
spacing law remains `Lblock^j*spacing`, while the regional side is separately
`K*Lblock^(depth+1)`.  Source SHA-256:
`F628EDDC8D74CF7AEE8855D29F836E0D2C772495CD532C56F7857FAB8873398B`.
The thirteen-declaration audit SHA-256 is
`416EC953D2929FBEE2C5B52B3157C0AE7790011FA33D05F4C2C2D9DDABEA86A2`.
Both pass the exact overlay text guard but remain unelaborated scratch; P5
is not compiler evidence and does not change a counter.

The complete thirty-three-file P0--P5 scratch closure is frozen in
`tmp/P0-P5-SCRATCH-MANIFEST.sha256`; the local byte gate reports `33/33`
matches.  Manifest SHA-256:
`C855D98D9983762DE0CE4B17BFC8E4BBD635CC17396BC8CF321AB4E0E7046129`.
The exact path list used by the text gate is
`tmp/P0-P5-SCRATCH-PATHS.txt`, SHA-256
`97818AF4872FEEFA8C1CA996F1C999AFFA5626A0EAFE78089B1F4DE0EB4EE033`;
the measured local result is `LEAN_OVERLAY_TEXT_OK files=33`.

Five scratch audit siblings now cover every public declaration in P0, P1,
P2a, P2b and P2c (10, 8, 26, 10 and 24 declarations respectively).  This
closes the static audit-coverage gap only: none of those `#print axioms`
commands has been executed, so no module is promoted, sealed or counted.
Seven further sibling audits cover every public declaration in the P3
support chain (9, 2, 8, 8, 2, 4 and 3 declarations).  The aggregate P3 audit
is now a distinct file from the exact three-readout sibling audit of the P3
physical endpoint.  This removes the earlier exception where one audit was
counted simultaneously as a sibling and as an 18-readout aggregate.  These
files are likewise static only.
The read-only promotion audit additionally reports
`P0_P5_PROMOTION_STATIC_OK sources=16 declarations=156`
with 156 unique promoted names.  The current exact figures are 16 sibling
audits, one additional P3 aggregate audit and 33 verified manifest members.
The gate now verifies the exact path-list order and every
manifest byte instead of merely trusting the frozen manifest; it caught and
repaired three stale P0/P1 rows after the scratch audit surface was made
explicit, then caught and repaired the non-source-order P4a readout.  It also
requires every sibling audit to import exactly its own producer.  Its SHA-256
is
`8236A55091263939325FA2982BC77A7FA6337C855C8D36225685EBE09972CC8D`.
Its synthetic companion
`tmp/test_p0_p5_promotion.py` (SHA-256
`4118DD82EC04CF29363CAADDA6EEF154EFE67CEB4112576F9180CE1BCEB5F873`)
passes a complete 33-file fixture and rejects both a manifest-consistent
wrong sibling import and an unrecorded source-byte change.
This checks only path/name/import/audit mechanics; it is not elaboration
evidence.

The deterministic read-only promotion preview
`tmp/audit_p0_p5_promotion_preview.py` (SHA-256
`74BFE687E4B68C0CF6E2311E838E7E94C2D87CF9614FAB936F57041917BF4ED4`)
now binds that exact 33-file raw manifest to the 16 proposed source paths,
their 16 exact sibling-audit paths and the separate P3 aggregate-audit path.
It rewrites only the declared `tmp.*` imports and the 156 provisional
identifiers, normalizes scratch-only status prose in the module docstring,
and installs one removable PRE-VALIDATION paragraph per promoted blob.  Its
visible-code comparison proves that comment normalization makes no additional
Lean-code change.  The current preview reports
`P0_P5_PROMOTION_PREVIEW_OK files=33 declarations=156` with zero target
collisions and promoted-content manifest SHA-256
`B594FF043253628185DDE308B73CC12D5BF583D4CAA79BAB5A4B784D11B543AA`.
It also resolves every promoted `YangMills.*` import against either this
exact batch or an existing tracked module, and rechecks the 16 sibling
readout orders plus the separate P3 aggregate readout after qualified-name
rewriting.
The synthetic companion `tmp/test_p0_p5_promotion_preview.py` (SHA-256
`B6EAA0B28A33A438CF80262BC63AA84D04F882E525CDE30BB3EE07995A061742`)
passes the full positive fixture and fails closed on source-byte drift, raw
manifest drift and a pre-existing tracked target.  The preview writes no
tracked source and is not compiler evidence.

The first stage now has a separate fail-closed instrument,
`tmp/promote_step8b24_c6c2_p0.py` (SHA-256
`DED29D3ECC1BD1E672FB65B2920E0FADEC9531821F6400E21759C0FB73799E85`).
It can materialize exactly the P0 source/audit pair, never P1--P5, and only
after the exact Step-8b.22 sealed source/audit hashes plus their core, map and
ledger evidence are present.  Its pair manifest is
`CCF1079CA2667310176146993CE75AB66DF7B42C65E1970E9997B5A02BA67146`.
On the current tree the exact Step-8b.22 prerequisite is sealed and the
promoter's read-only dry run succeeds; it still cannot write P0 before the
separate P0--P9 compiler evidence is green.  The synthetic test
`tmp/test_promote_step8b24_c6c2_p0.py` (SHA-256
`A7B6947FDBB9EC9F25F06934B21C758C1A18432E64A100755C14CE22B69BE4F3`)
verifies a read-only dry run, two exact writes with one PRE-VALIDATION block
each, no scope leak into P1, syntax/scope generation of the exact two-stage
Colab runner, and fail-closed behavior after a committed byte change to the
sealed prerequisite.  The runner generator
`tmp/generate_step8b24_c6c2_p0_validation_runner.py` has SHA-256
`180A9ED70D402909F63E5A03C232D1D5843D3FC51E87EE9B5677F7B769936AD8`.
This is instrumentation only, not a P0 elaboration or seal.

The first fresh Colab elaboration with the complete nine-target project
frontier materialized all `8562` prerequisite jobs and then stopped at P0:
the three physical matrix-norm signatures did not open
`Matrix.Norms.L2Operator`.  The executed notebook is preserved with SHA-256
`F13A4583CC994F561071F3C12211E5C745C5F35514DC5A5FA3B30D89DAD8B4CA`.
This is a real first elaboration failure, not compiler evidence.  Checkpoint
`3af413563b2f71c250e9e7bbd4972efca436ad55` opens the same scope in every
P0--P5 source that exposes this matrix norm, without changing a theorem
statement, constant or hypothesis.  Its 39-file manifest is
`71DA54FE12B77F7288A33C4EDB6130733B288CC0B2BA3E3A3D081E0469E4F3F9`;
the rerun remains PRE-VALIDATION until its own Colab verdict.

## Stop condition

P0--P5 close only C6c.2.  They do not produce the CMP96 Dirichlet defect,
the random-walk closure, the four-action regional certificate, window 15 or
a terminal `TermSource`.

## Proposed restartable module order

No file in this list exists as promoted Lean source yet.  Each source module
must have one sibling audit and retain PRE-VALIDATION until its own cold seal.

0. `BalabanCMP99SourcePoincarePositiveRadiusReachability` (upstream scalar
   reachability: a positive radius jointly inhabiting the closed `Ubar`
   budget and the one terminal Poincare premise; it is not a P0--P5 operator
   producer and does not move their declaration count);
1. `BalabanCMP99SourceCanonicalPrefixTower` (P0);
2. `BalabanCMP99SourcePrefixPoincare` (P1, including coefficient
   monotonicity);
3. `BalabanCMP85SourcePrefixGreen` (P2a);
4. `BalabanCMP85Eq221EffectiveQuadratic` (P2b);
5. `BalabanCMP85Eq230CoarseCovariance` (P2c);
6. `BalabanCMP85BlockGaussianRecurrence` (generic typed algebra only);
7. `BalabanCMP85Eq241Eq242PhysicalGreenRecurrence` (P3 specialization);
8. `BalabanCMP85Eq230BaseCovariance` (P4a, the separately generated
   `G_1 = C^(0)` identity);
9. `BalabanCMP85Eq243PhysicalGreenScaleSum` (P4b);
10. `BalabanCMP89Eq234PhysicalGreenScaleDictionary` (P5, preserving
   independent `Lblock` and regional `K`).

A later module may merge adjacent leaf bricks only after their declarations
have elaborated; the semantic boundaries P2b/P2c and generic/physical P3 may
not be merged away in the public audit.
