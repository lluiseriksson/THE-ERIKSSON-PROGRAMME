# Step 8b.24 / C6c.8 - CMP99 Corollary 3.6 gauge transport

Status: STATIC DESIGN ONLY.  Nothing in this document is compiler-verified,
promotable or a producer of a terminal field.

## Source gate

The local renders of CMP99 printed pp. 395, 397 and 408 fix the source
mechanism.

1. Equation (3.31) conjugates the covariant site Laplacian by the pointwise
   adjoint action `R(u)`.
2. Equation (3.32) intertwines every retained average `Q'_j(U)` with the fine
   action `R(u(x))` and the induced coarse action `R(u(y))`.  Consequently
   `Q'^* a Q'` conjugates by the fine action.
3. Equations (3.33)--(3.34) then conjugate the precisions and their Green
   inverses.
4. Corollary 3.6 is not a free operator equality.  It starts from a regular
   configuration satisfying (3.35), a source domain `Omega'_0` contained in
   one of the corresponding regular cubes, and the scalar gate
   `O(1) * M * alpha0 <= alpha1`.  The regularity witness supplies a gauge
   transform `u` for which `U^u = exp(i eta A)` and the transformed background
   satisfies the near-identity hypotheses of Corollary 3.5.  Gauge invariance
   then transports all of Theorems 3.1--3.3 back to `U`.

Thus C6c.8 must transport the whole source package.  Supplying an equality
between a caller-chosen Green and the canonical regional Green would rename
the conclusion and is rejected.

## Measured reusable tree substrate

The tree already contains more than the old frontier row recorded:

- `GaugeConfig.gaugeAct` is the literal endpoint action on the background.
- `SUNAdjointModel.adCLM`, `ad_mul`, `ad_inner`, `ad_inv_apply_ad` and
  `norm_ad` supply the pointwise real-orthogonal adjoint representation.
- `cmp99ContourHolonomy_gaugeAct` proves endpoint covariance of the literal
  contour holonomy.
- `cmp99AdjointBlockTransport_contour_gaugeAct` proves the fine-to-coarse
  adjoint-transport intertwiner.
- `cmp99RegionalFineGaugeAct` and `cmp99RegionalCoarseGaugeAct` are the
  source-shaped pointwise actions on active zero-cochains.
- `cmp99AdjointBlockAverageCLM_contour_gaugeAct` proves the complete one-scale
  Eq.-(3.32) intertwiner.
- `cmp99PhysicalUbarGaugeConfig_gaugeAct` proves gauge covariance of the
  recursively generated next background.
- The regional restriction/extension maps, literal physical precision and
  inverse-by-coercivity Green already exist.

These results make the average part of (3.32) a reusable theorem, not an open
axiom.  They do not yet give Corollary 3.6.

## Precisely missing theorems

### C6c.8a - proof-carrying regional gauge isometries

Package the existing fine and coarse pointwise actions as real linear
isometric equivalences, with inverse induced by `fun x => (u x)^-1`.  Prove
pointwise application, inverse, norm and support preservation.  Region
restriction and extension-by-zero must commute with these actions by named
theorems.

This is algebraic infrastructure.  It must not take any operator covariance as
a field.

Static implementation measurement (2026-08-17): this prefix is finite and the
needed mechanism already exists at the fixed Mathlib pin.  The scratch pair
`BalabanCMP99RegionalGaugeIsometry.draft.lean` / `...Audit.draft.lean`
contains 16 declarations and 16 axiom readouts.  Its three equivalences are
literal dependent lifts

```text
LinearIsometryEquiv.piLpCongrRight 2
  (fun x => rho.adLinearIsometryEquiv (...))
```

on the ambient fine, regional fine and regional coarse `PiLp` fields.  The
regional actions are definitionally the already-sealed
`cmp99RegionalFineGaugeAct` and `cmp99RegionalCoarseGaugeAct`; their inverse
actions, norm and function support are derived from the fibre equivalences.
Restriction and zero extension commute by pointwise theorems, with the latter
using a carrier case split and no support premise.  The fail-closed static
preview reports 16/16 and checks that no covariance/final-bound field has been
introduced.  This remains PRE-VALIDATION: it has not been elaborated and does
not move any counter.

### C6c.8b - covariant derivative and Laplacian intertwiners

For the literal transformed background prove the source orientation

```text
D0(U^u) (R(u) phi) = R_bond(u) (D0(U) phi),
Delta'_U^u (R(u) phi) = R(u) (Delta'_U phi),
```

where the positive-bond action is based at the source vertex.  Derive the
Laplacian identity through adjoints/isometries; do not postulate it.  Then
specialize it through regional restriction/extension to the literal Dirichlet
operator.

The source-domain containment is portante here: a local gauge witness may be
extended outside the regular cube only after proving that the Dirichlet
precision reads no background data beyond the protected domain/collar.  A
bare `Omega subset cube` rewritten by `simp` is not an accepted locality proof.

Static implementation measurement (2026-08-17): the ambient derivative,
adjoint/Laplacian algebra and global-gauge regional corollaries form an
eleven-declaration
scratch pair, `BalabanCMP99CovariantD0GaugeIntertwiner.draft.lean` and audit.
The positive-bond isometry is based literally at `b.1`, the source of the
positive representative.  The ambient theorem expands
`GaugeConfig.gaugeAct`, applies `rho.ad_mul` twice and cancels the target action
with `rho.ad_inv_apply_ad`; it accepts no covariance equality.  Since
`cmp99ActiveRegionSourceCovariantD0CLM` is definitionally

```text
spacing^-1 • covariantD0CLM(U) ∘ extendZeroZeroCLM(Omega),
```

the regional corollary follows from the C6c.8a zero-extension theorem and
linearity.  This does **not** discharge the source locality gate: that gate is
now located precisely in C6c.8f, where the gauge witness known on the regular
cube must be extended to a global transform without changing any background
datum read by the regional operator.  The scratch endpoint derives the
regional Laplacian intertwiner from the
operator-form `D0` theorem by a generic isometric-adjoint lemma; it does not
postulate Laplacian covariance.  Static preview is 11/11; nothing here has been
elaborated or counted.

### C6c.8c - retained tower covariance

Lift the sealed one-scale average intertwiner through every canonical retained
scale.  The induction must use:

- the literal recursive background,
- `cmp99PhysicalUbarGaugeConfig_gaugeAct` for the next background, and
- the induced coarse gauge function at canonical block basepoints.

Its endpoint is an exact intertwiner for the canonical retained `Qprime`, not
an equality between two independently chosen towers.  This is the missing
multiscale part of Eq. (3.32).

Static constructor audit (2026-08-17) exposes a necessary refinement.  The
only canonical retained constructor currently in the tree,
`cmp99SourceGeneratedRetainedPhysicalTower`, requires `fineSmall` for its
input background and propagates that hypothesis down the literal `Ubar`
chain.  Corollary 3.6 supplies such smallness for `U^u`, not for the original
regular background `U`.  Consequently the following superficially natural
implementation is rejected:

```text
build canonicalTower(U) and canonicalTower(U^u) independently;
prove that they intertwine.
```

It would add an unprinted near-identity hypothesis on `U` and would exclude
the regular configurations for which the corollary is needed.

The source-faithful construction order is instead:

1. construct the existing canonical retained tower on the near-identity
   representative `U^u`;
2. define the original-side regular tower by transporting every retained
   field and `Qprime` back through the inverse fine/coarse gauge isometries;
3. identify each transported one-step average with the literal contour
   average in the transported-back background using
   `cmp99AdjointBlockAverageCLM_contour_gaugeAct`;
4. identify the next transported-back background recursively using
   `cmp99PhysicalUbarGaugeConfig_gaugeAct` and the induced
   `coarseTransform u`.

Step 3 applies to the exact physical transport already used by the tower:
`cmp99SourceWeightedPhysicalTransport` unfolds to
`cmp99AdjointBlockTransport rho (cmp99ContourHolonomy
cmp99BlockContainedContourSystem background)`.  It is not a second contour
choice.  Before step 4, one additional source lemma is required: covariance
of `cmp99SourceBaseCoarseBackground`, derived from
`OrientedLatticePath.holonomy_gaugeAct` for the literal straight coarse-bond
path.  No such named lemma currently exists in the tree.

This transported-back object is a new **regular-background canonical
constructor**, not permission to choose an arbitrary tower.  Its public data
must be generated from `(U, u, canonicalTower(U^u))`; it must not accept an
original-side tower or any `Qprime` equality as an argument.  When the old
near-identity constructor is also definable on `U`, a comparison theorem may
show that the two constructors agree, but that comparison is not a premise of
Corollary 3.6.

There is enough lower-level API to keep the transported-back backgrounds
literal.  `cmp99SourceRegionalScaleDataOfDeviationBudget` constructs the
source contours and `Ubar` from a direct no-winding deviation bound, without
requiring linkwise `fineSmall`.  Gauge conjugation preserves that deviation
norm, so the bound on `U^u` can be transported back to `U`.  However the
public normalized wrapper currently exposes only `ofFineSmall`; its raw
constructor is private.  C6c.8c therefore needs a public, source-fixed
`CMP99SourceNormalizedRegionalScale.ofDeviationBudget` whose weight is
definitionally `cmp99SourceBlockAverageWeight M d` and whose remaining data
is exactly `cmp99SourceRegionalScaleDataOfDeviationBudget`.  This constructor
removes the false `fineSmall U` premise without weakening the literal Ubar
recursion.

The deviation transport itself must be a theorem: first use
`UbarDeviationLogArg_gaugeAct` (already present below the group-level
covariance in `Ubar.lean`), then prove equality of the concrete matrix norm
under special-unitary conjugation by applying the existing contractive bound
in both directions.  A caller-supplied deviation bound on `U` is rejected.

Finite implementation ladder for C6c.8c:

| brick | exact output | status |
|---|---|---|
| C6c.8c1 | `cmp99SourceBaseCoarseBackground (U^u) = (baseCoarse U)^(coarseTransform u)` | scratch theorem written; PRE-VALIDATION |
| C6c.8c2 | equality of `‖UbarDeviationLogArg‖` under the same gauge conjugation | scratch theorem written from group equality plus two-sided norm bound; PRE-VALIDATION |
| C6c.8c3 | private regular/small scale pair, fixed weight `M^{-d}`, deriving the original-side budget from `fineSmall (U^u)` | scratch pair constructor written; PRE-VALIDATION |
| C6c.8c4 | covariance of that pair's literal direct-budget `nextBackground` | block/config theorem plus scale-pair endpoint written; PRE-VALIDATION |
| C6c.8c5 | one-step weighted-average intertwiner for the exact source transport | scratch specialization written by definitional reduction; PRE-VALIDATION |
| C6c.8c6 | recursive regular-background retained tower generated from `U^u` and inverse gauge transport | design fixed; constructor absent |
| C6c.8c7 | exact retained-prefix `Qprime` intertwiner for every `r` | induction endpoint; absent |

No brick in this ladder may take the output equality of a later row as an
input.  In particular c6 accepts the regularity witness and the canonical
tower on `U^u`, not an original-side tower; c7 is proved from the recursive
constructor equations, not stored as user data.

Public-interface audit adds one hard gate before c6.  The existing
`CMP99SourceRetainedPhysicalTower` exposes `nextAverage` and
`towerAt_succ_Qprime`, but it does **not** expose the physical background
consumed by each `nextAverage`, nor a theorem identifying that field with
`cmp99SourceWeightedPhysicalTransport` at the corresponding recursive Ubar
background.  Constructor privacy prevents a forged tower, but it does not let
a downstream proof recover this hidden equation.  Therefore covariance may
not be proved for an arbitrary retained-tower argument from the current public
fields.

Accepted repairs are deliberately narrow:

- extend the retained structure with a constructor-generated `backgroundAt`
  chain, its exact successor-Ubar equation and an exact `nextAverage_eq`; or
- construct a private `CMP99SourceGaugeTransportedRetainedPair` recursively,
  containing the original and transformed physical prefixes together with
  their background covariance and derived `Qprime` intertwiner.

The paired constructor is preferable if extending the old structure would
force unrelated consumers to carry new fields.  In either repair, the
background and intertwiner data are filled only by the private recursive
constructor.  Adding a public `nextAverage_eq` or `backgroundCovariance` input
to the final source theorem is rejected as obligation renaming.

The existing theorem `cmp99PhysicalUbarGaugeConfig_gaugeAct` is not yet the
exact c4 endpoint: it targets the older common-radius constructor, whereas
`CMP99PhysicalRegionalScaleData.nextBackground` unfolds to
`cmp99PhysicalUbarGaugeConfigOfDeviationBudget`.  C6c.8c4 must therefore prove
the corresponding direct-budget covariance theorem.  Its matrix content is
still the existing `Ubar_gaugeAct`; the missing adapter identifies the
coercion of `cmp99PhysicalUbarBlockOfDeviationBudget` with that literal Ubar
using `cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe`, then handles the
negative orientation through `GaugeConfig.map_reverse`.  Reusing the older
theorem by definitional equality would be false and is not accepted.

The scratch pair
`BalabanCMP99SourceGaugeDeviationTransport.draft.lean` / `...Audit.draft.lean`
contains the c1--c2 prefix and the c4 block/config adapters (five declarations:
reusable matrix isometry, physical deviation norm, direct-budget block
coercion, direct-budget Ubar configuration covariance, and coarse-background
covariance).  The fail-closed preview and overlay text gate report 5/5 and no
placeholders.  This is syntax/mechanism evidence only: no Lean elaboration or
axiom output exists yet.

The public low-level budget wrapper in c3 is infrastructure only.  The
source-facing endpoint must have the shape

```text
ofGaugeSmall
  (u : GaugeTransform ...) (U : GaugeConfig ...)
  (fineSmallT : fineSmall (gaugeAct u U))
  : CMP99SourceNormalizedRegionalScale Omega U
```

and must construct its deviation certificate internally by c1--c2.  The
final Corollary-3.6 producer may call `ofGaugeSmall`; it may not expose the
low-level `deviation_bound` argument.  This distinction keeps a useful
constructor API without turning the no-winding conclusion into a renamed
hypothesis at the source endpoint.

The independent c5 scratch pair
`BalabanCMP99SourceWeightedPhysicalGaugeCovariance.draft.lean` / audit reduces
the exact source-weighted operator to
`cmp99AdjointBlockAverageCLM_blockContainedContour_gaugeAct`; the static
preview reports 1/1 and the text gate is green.  It accepts neither a
transport equality nor a `Qprime` equality.  It remains unelaborated.

The c3--c4 scratch pair
`BalabanCMP99SourceGaugeRegularScalePair.draft.lean` / audit packages the
original and transformed literal scale data behind a private constructor.  Its
only analytic input is `transformedSmall` for `gaugeAct u background`; the
original deviation bound and `nextBackground_gaugeAct` are local derived
proofs.  Static preview is 2/2 and the overlay text gate is green.  This is the
chosen replacement for exposing a public low-level deviation hypothesis at
the Corollary-3.6 endpoint; it remains unelaborated.

#### C6c.8c6--c7 - measured retained-tower boundary

Static inspection of `CMP99SourceRetainedPhysicalTower` and
`CMP99SourceActiveRegionChain.weightedQprimeTower` fixes the remaining design
choice.  The retained public structure exposes `towerAt`, `nextAverage` and
the exact successor composition, but it deliberately does not expose the
physical background from which each `nextAverage` was generated.  The typed
active-region chain has the same boundary: its definition recurses through
the literal `Ubar` backgrounds, but those backgrounds are not recoverable from
the resulting tower.  The existing bridge identifies only `towerAt (Fin.last
depth)` with the generated `weightedQprimeTower`; it does not identify every
prefix or its hidden one-step physical data.

Consequently neither of the following is accepted:

- construct two independent canonical retained towers, since the original
  one would require the false extra premise `fineSmall U`;
- add public fields supplying per-prefix backgrounds, average equalities or
  final `Qprime` intertwiners, since those would rename the source obligation.

The chosen c6--c7 object is instead a **private gauge-transported retained
pair**, constructed by one recursion on the common depth.  Its successor
branch must:

1. call the c3--c4 regular/small scale-pair constructor on `(U, U^u)`;
2. use the c5 exact source-weighted one-step covariance theorem;
3. recurse on the two internally generated coarse backgrounds, related by
   the derived `nextBackground_gaugeAct` theorem;
4. prepend the two literal one-step averages to the paired tail towers; and
5. derive, rather than accept, the intertwiner for every retained prefix and
   hence Eq. (3.32) for the terminal `Qprime`.

This local recursion avoids needing a global closed form for iterated
`coarseTransform u`: each successor passes the transform produced at that
scale to the tail.  It also leaves the existing retained-tower API unchanged,
so unrelated consumers do not acquire proof fields that only Corollary 3.6
needs.  A later public theorem may project the two ordinary retained towers
and their derived prefix intertwiners from the private pair; no equality is a
caller input.

### C6c.8d - precision and Green conjugation

Combine C6c.8b and C6c.8c to prove conjugation of the literal

```text
cmp99OmegaSourcePhysicalGaugePrecision
```

and derive conjugation of the internally constructed Dirichlet Green by
inverse uniqueness.  The Green equality must not be a constructor parameter.
The same conjugation route must cover the coarse middle/inverse if C6c.7 is
packaged at the full Proposition-2.2 level; Corollary 3.6 transports Theorems
3.1--3.3 together.

The scratch pair
`BalabanCMP99SourceGaugeTransportedPrecisionGreen.draft.lean` / audit now
implements the exact algebraic route.  It builds the two precisions from the
literal covariant Laplacians and the terminal members of the private retained
pair; transports `Qprime.adjoint.comp Qprime` using the derived terminal
isometry; transports coercivity backwards with the same constant; constructs
both Greens through `covarianceOfIsCoerciveCLM`; and proves their intertwiner
by injectivity/inverse uniqueness.  No precision, coercivity or Green equality
is an input.  Static preview is 8/8 and the text gate is green; the module is
not yet Lean-elaborated.

The generic pair is coefficient-polymorphic and remains valid substrate for
the source-faithful C6c.2 Green.  Its scalar argument must be instantiated by
the literal CMP85 prefix coefficient generated from
`cmp99SourceMassParameter a L j`, and its coercivity proof must be the C6c.2
prefix coercivity theorem.

The second scratch pair
`BalabanCMP99SourceGaugeRegularGeneratedGreen.draft.lean` / audit is now
classified as an **auxiliary Poincare-normalized specialization only**.  It
uses `transformedTerminal_eq_generated` to rewrite the transformed precision
to `cmp99SourceGeneratedPhysicalPrecision`, whose `Qprime.adjoint * Qprime`
coefficient is `cmp99SourceGeneratedPhysicalMass`.  C6c.2 instead constructs
the printed CMP85 coefficient family from one base `a`; the depth-one scalar
comparison already shows that the two coefficients are not universally
definitionally equal.  No theorem in the tree equates the two coefficients,
their precisions, or their Greens.

Consequently this second pair must not be promoted or cited as the C6c.8d
source endpoint for C6c.7.  Its algebra may be retained as a proof template,
but the admissible source specialization after C6c.2 must:

1. instantiate the generic transported precision with the exact C6c.2
   counting/source-weighted coefficient at the selected prefix;
2. obtain transformed-side coercivity from the internally generated C6c.2
   theorem, not from `isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision`;
3. identify the transformed inverse with the C6c.2/CMP96 Green by the two
   inverse equations; and
4. transport that same Green and all C6c.7 actions to the regular background.

No equality between the Poincare-normalized and CMP85 source Greens may be a
constructor input or a `simpa` step.  The f2g/f5 retained-tower promotion is
unaffected because it constructs only the common `Qprime`/background
infrastructure and no Green or action bound.  C6c.8d remains PRE-VALIDATION
and its final source specialization is not yet written.

### C6c.8e - transport of the action bounds

Prove that the fine/coarse gauge isometries preserve:

- source-owner support,
- pointwise and owner-sup norms,
- the output-fixed owner-weighted kernel norm,
- left derivative, right-adjoint derivative, Holder and Laplacian actions.

Then transport the common C6c.7 amplitude and rate unchanged to the canonical
regional Green.  Gauge invariance of the final inequalities must be a theorem
derived from these isometries, not a Boolean or a field of a certificate.

The scratch pair `BalabanCMP99GaugeActionBoundTransport.draft.lean` / audit
implements the norm-and-support algebra which precedes that specialization.
It proves that coordinatewise norm preservation implies exact preservation of
`finitePiLpSupNorm` and of every `FinitePiLpSupportedInOwner` fibre, and that
an exact source/target intertwiner therefore transports
`FinitePiLpTypedBlockLocalizedSupBound` with unchanged amplitude, rate, owner
maps and distance.  A separate composition lemma keeps the orientation of
`D G`, `G D*` and `Delta G` explicit.  The regional-site and positive-bond
gauge actions discharge the required pointwise norm premise from
`SUNAdjointModel.norm_ad`.  Static preview is 6/6 and the text gate is green;
the pair is not Lean-elaborated.

This pair deliberately does **not** construct the four physical action
bounds: their transformed-side C6c.7 producer is still absent.  Once C6c.7
exists, C6c.8e must derive the four operator intertwiners from C6c.8b--d and
apply this algebra, rather than receive any of the final inequalities as an
input.

### C6c.8f - source regularity constructor

Introduce a source-facing witness for CMP99 (3.35) whose mathematical data are
the local gauge transform and the small logarithmic representative on the
regular cube, together with the domain/collar containment and the printed
scalar comparison `O(1) * M * alpha0 <= alpha1`.  From that witness construct
the transformed near-identity inputs consumed by C6c.7 and then apply
C6c.8a--e.

It is legitimate for the final theorem to assume the named CMP99 regularity
hypothesis.  It is not legitimate to assume the desired Green/operator
dictionary or the transported action bounds.

#### Measured source and API boundary (2026-08-18)

The primary article is Project Euclid `cmp/1103942769`, journal p. 396
(PDF p. 8).  Primary render `tmp/pdfs/cmp99-p396.png`
(`15BDDA14DBE560AFE172128D4FDF5234E9B0D6F652F8B811B072A878179F452E`)
shows that every regular cube has a unique `0 <= j <= k`, is contained in
`B^j(Lambda_j) union B^(j+1)(Lambda_(j+1))`, meets
`B^j(Lambda_j)`, is a union of big blocks at that scale, and has size
`O(1) M L^j eta` with the printed convention **`O(1) >= 10`**.  For every such
cube there exists a gauge transform `u` such that
`U^u = exp(i eta A)` and, at the cube's scale `j`,

```text
|A|    < O(1) M alpha0 (L^j eta)^-1,
|nabla^eta A| < O(1) M alpha0 (L^j eta)^-2            (3.35)
```

The p. 396 render shows an ordinary fine-lattice forward derivative in (3.35),
not the background-covariant tensor introduced later.  The local render of
printed p. 397 independently confirms (3.39) as the supremum norm of the full
background-covariant derivative,
`max_(mu,nu) sup_x |(D^U_mu A_nu)(x)|`.  That later norm belongs to the
propagator/action estimates and must not be used as the regularity witness of
(3.35); nor is either object the antisymmetrized plaquette curl.  The exponent,
the common cube/scale and the role of the two (3.35) bounds in Corollary 3.6
are supported by the primary render and its OCR companion.  The remaining
gate is type-theoretic rather than visual: the terminal `Lambda_(k+1)` value
must be derived from
`Omega_(k+1) = empty`, and the printed cube/large-block size law must be
represented without replacing the source cube by an arbitrary finite carrier.

on the printed cube.  Corollary 3.6 then assumes `Omega'_0` is contained in
that cube and `O(1) M alpha0 <= alpha1`; it applies Corollary 3.5 to the local
small representative and transports the conclusions by gauge invariance.
The source does **not** state global linkwise smallness on the whole torus.

Static inspection exposes a concrete mismatch with the current constructor
API.  Both `cmp99SourceRegionalScaleDataOfFineSmall` and the generated retained
tower consume

```text
forall e : ConcreteEdge d N, norm (background e - 1) <= epsilon,
```

globally.  Moreover `CMP99PhysicalRegionalScaleData` constructs its Ubar
background for every coarse physical bond; the fact that the eventual
Dirichlet operator is restricted to `Omega` does not make that global premise
definitionally unused.  Extending the local gauge transform by the identity
outside the regular cube cannot turn the local estimate (3.35) into this
global premise.  Feeding the existing argument directly would therefore
silently strengthen Corollary 3.6 and is rejected.

The repair is a finite locality ladder, not an additional analytic axiom:

| brick | exact output | status |
|---|---|---|
| C6c.8f1 | source witness carrying the regular cube, cube-local gauge, logarithmic representative, the two literal (3.35) bounds and `O(1) M alpha0 <= alpha1` | PRE-VALIDATION scratch materialized; not elaborated |
| C6c.8f2 | named read-carrier/collar theorem for the regional Laplacian, source contours and every retained one-step average | f2a--f PRE-VALIDATION scratch materialized through the exact dependent read carrier and retained-`Qprime` induction; f2g.0--f2g.5 now written through the explicit source-region dictionary, but wholly unelaborated and uncounted |
| C6c.8f3 | localized deviation/Ubar scale constructor indexed only by coarse bonds whose complete source contours lie in that read carrier | f3a--f PRE-VALIDATION scratch materialized through the private retained-prefix package; not elaborated or counted |
| C6c.8f4 | derive the required local near-identity link bound from `U^u = exp(i eta A)` and the (3.35) amplitude bound; no `fineSmall` field in the witness | PRE-VALIDATION scratch materialized with radius `2 * alpha1`; not elaborated |
| C6c.8f5 | instantiate the retained pair on `Omega'_0`; then consume the still-absent C6c.7 bounds and apply C6c.8a--e | retained-pair/Qprime prefix PRE-VALIDATION; C6c.7 composition absent |

C6c.8f2 is portante.  It must prove that replacing the transformed background
outside the protected collar leaves the literal regional precision, retained
Qprime and Green unchanged.  A caller-supplied equality between those
operators, or a global `transformedSmall`, would rename the missing locality
theorem and is not accepted.

Primary-render correction (2026-08-18): printed p. 408 states the geometric
premise `Omega'_0 subset square`; it does **not** state that
`regions.retainedFineReadBonds` is itself contained in the regular cube.
Consequently the f4 premise
`CMP99Eq335RetainedFineReadCarrierInsideRegularCube` is only an honest
intermediate debt.  It may not survive as a public source hypothesis of the
final constructor.  The missing geometric brick is now named:

```text
C6c.8f2g : retainedFineReadBonds endpoints subset Omega'_0
           from the typed active-region chain and literal source contours;
           compose with the printed Omega'_0 subset square afterwards.
```

The intended induction must carry **both** endpoints of every retained
positive bond.  The head transported-average carrier is generated by
`cmp99BlockContainedContourSystem_staysIn` inside complete active blocks.  In
the successor pullback, the induction hypothesis must show that both coarse
endpoints of every retained tail bond lie in
`cmp99ActiveCoarseRegion Omega`; only then do block saturation and the literal
Gamma1/Gamma2/Gamma3/base paths place their fine endpoints back in `Omega`.
The existing lemma
`physicalBondOfEdge_fst_mem_blockOf_of_staysIn` controls only the positive
representative's source and is insufficient by itself.  No containment result
is counted until this strengthened endpoint induction is elaborated and
audited.  In particular, one must not infer locality merely from the fact that
the source block of a coarse bond is active; a boundary-crossing target would
invalidate Gamma2/Gamma3 containment.

The finite six-subbrick route f2g.0--f2g.5 and its acceptance gates are recorded in
`tmp/STEP8B24-C6C8F2G-RETAINED-CARRIER-CONTAINMENT-DESIGN.md`.

#### Literal regularity dictionaries still absent (measured 2026-08-18)

Two tempting reuse paths are type-correct in spirit but source-wrong.

First, (3.35) uses the ordinary fine forward difference of the logarithmic
one-cochain `A`.  It does not use the full background-covariant tensor of
(3.39), `covariantD0CLM`, or the antisymmetrized plaquette operator
`covariantD1CLM`.  C6c.8f1 may not accept an arbitrary function called
`derivative` together with its desired bound.  The named source dictionary is:

```text
C6c.8f0a : CMP99 (3.35) ordinary `nabla^eta` one-cochain derivative
           -> literal periodic forward-difference tensor and PiLp-infinity norm.
```

The separate (3.39) covariant tensor remains relevant downstream to C6c.8e
and the operator-action bounds; it is not an input to the regular-cube
regularity certificate.

Second, `cmp99SourceTildePiLargeBlocks` is not the regular-cube class of
(3.35).  It is the special concentric family `tilde Pi^n` introduced later in
Section C.  The regularity paragraph instead assigns a unique scale index to
each cube, requires the printed stratum/intersection conditions, and requires
the cube to be a union of large blocks at that scale.  Reusing the concentric
family would silently restrict Corollary 3.6.  C6c.8f1 consequently needs a
second named source dictionary rather than an arbitrary `Finset` carrier:

```text
C6c.8f0b : source regular cube = scale index + literal large-block carrier
           + stratum/intersection laws + physical site/bond realization.
```

The exact exponential side does have a genuine existing bridge:
`cmp98PhysicalSuIncrement` constructs the special-unitary exponential of a
`PhysicalGaugeOneCochain` coordinate and its coercion theorem identifies the
matrix with `physicalMatrixExp`.  C6c.8f1 should reuse that object after
C6c.8f0a--b, rather than introduce a free exponential chart.

Thus the corrected finite ladder is ordered

```text
C6c.8f0a + C6c.8f0b -> C6c.8f1 -> C6c.8f2 -> C6c.8f3
                    -> C6c.8f4 -> C6c.8f5.
```

This is a design boundary, not a compiler result.  Neither dictionary is
counted as present, and no tracked source is changed by this audit.

#### C6c.8f0a scratch materialization (2026-08-18)

The first candidate,
`tmp/BalabanCMP99Eq335PhysicalCovariantDerivative.draft.lean`, identified
(3.35) with the later covariant tensor (3.39).  The p. 396 render refutes that
identification.  The candidate and its audit remain in scratch with explicit
`RETRACTED` headers; they were never promoted, compiled or counted.  The
diagnostic is preserved in
`tmp/C6C8F0A-COVARIANT-DERIVATIVE-RETRACTION.md`.

The corrected
`tmp/BalabanCMP99Eq335PhysicalForwardDerivative.draft.lean` fixes the operator
side without a free derivative input or a background field.  It reuses the
literal `torusForwardDiff` and scales it by `eta^-1`, producing the tensor

```text
(x, mu, nu) |-> eta^-1 * (A_nu(x + mu) - A_nu(x)).
```

Its target is `PiLp infinity`, so the ambient norm is the literal finite
component maximum appropriate to the ordinary (3.35) bound.  Amplitude and
forward-derivative bounds remain separate predicates.  The companion audit
has one source-facing readout.  Current corrected scratch hashes are

```text
65634E403FC0CF35029E063CB4EF35D494B653F0EF5EEC290BF80DD06CAADB6C  source
72025C310AC02D756E7C9005FC006AAE42CA155D9859B7A36CEFA2310705FDF6  audit
```

This is PRE-VALIDATION scratch only: no `.olean` or oracle output exists.  A
four-file f0a/f0b overlay text gate sees no `sorry`/`admit`, and every file
begins with its import.

C6c.8f0b is now materialized in PRE-VALIDATION scratch as
`BalabanCMP99SourceRegularCube.draft.lean` plus its seven-readout audit.  It
derives the terminal adjacent stratum from the literal terminal region and
`global.final_empty`; constructs the scale-`j` big-block cube from a periodic
base and side `geometryFactor * M` with `geometryFactor >= 10`; derives the
fine carrier by the existing `fineBlock` map; and stores exactly the two
printed stratum clauses plus uniqueness of `j`.  It accepts neither a free
carrier, a terminal stratum nor a `domainOf` map.  Current scratch hashes are

```text
99D178132F3869215529C8EC09C980BB2F06112B825A0860F4B442521790527B  source
433DE67E650961C902F62B26B12A5EE6646C33B5DBC73C1E3FC42102B6514966  audit
```

The two-file text gate is green; no Lean elaboration or oracle output exists.
The source/extraction rationale is recorded in
`tmp/CMP99-P396-REGULAR-CUBE-EXTRACTION-CARD.md` (SHA-256
`1FB3346683410DEC10BA0D333183132A9C57FE7F251449B0A173B7198502A11A`).

#### C6c.8f1 scratch materialization (2026-08-18)

`tmp/BalabanCMP99Eq335PhysicalRegularityWitness.draft.lean` packages the two
f0 dictionaries without globalizing the source statement.  Its gauge has type

```text
{x // x in cube.carrier} -> SU(Nc),
```

and `U^u = exp(i eta A)` is required only on the proof-carrying subtype of
positive bonds whose source and shifted target both belong to that same cube.
There is no global `GaugeTransform` and no global transformed-background
equality.  The logarithmic representative is stored in the existing periodic
physical one-cochain coordinate solely because the literal `SU(N)` chart
expects that coordinate; all f1 laws read it on the cube.  Its exterior values
cannot be consumed until f2 proves independence from exterior extensions.

The two bounds use the corrected ordinary `nabla^eta A` dictionary and the
literal scale spacing `L^j eta`.  The geometric factor of the same cube occurs
in both majorants and in the visible scalar gate
`geometryFactor * Mlarge * alpha0 <= alpha1`.  The fine lattice factor `L` and
the source large-block multiplier `Mlarge` are distinct parameters.

Current scratch hashes are

```text
14A29EC9FD6A0F75C22F3D38E2F8339AD80A8A2E8BCC732C4536087366A6A59E  source
488A9B0B20F0F67B94A4A3EA1B21BB9A9325E9246512A46C0870E3ED69DBF4E4  audit
```

The combined six-file f0a/f0b/f1 text gate is green and the audit queue names
eight readouts.  This is text/mechanism evidence only: no Lean elaboration or
oracle verdict exists, and f1 is not a producer until its dependencies and the
module itself receive a sanctioned seal.

#### C6c.8f2a exact Laplacian read carrier (2026-08-18)

Static unfolding found that the Dirichlet covariant derivative does not read
only the internal active bonds.  Because its input is first extended by zero,
`D_U phi` can be nonzero on every positive bond with **either** endpoint in
`Omega`.  The exact background read carrier is therefore the one-bond collar

```text
{b | source(b) in Omega.sites or target(b) in Omega.sites}.
```

`tmp/BalabanCMP99Eq335PhysicalRegularityLaplacianLocality.draft.lean`
constructs this carrier and derives equality of the literal regional
covariant derivatives, then of `D^* D`, from pointwise background agreement
there.  It does not receive either operator equality as an input.

The same module canonically extends the cube-local gauge by the identity, but
asserts no source law outside the cube.  Under the explicit geometric gate
that the one-bond collar lies in the cube, f1 proves agreement on every read
bond with the global positive-bond configuration generated by the physical
`SU(N)` exponential.  The first f2 endpoint is then the exact regional
Laplacian equality derived through the generic read-carrier theorem.

Current scratch hashes are

```text
C61E655058E81BF2E20C13F9426DB690C49E7C80EA3C2A3886156D629C0E3BCF  source
F503B6920E9C7DB5659916E22FBBA408BDE50979BC43C58CF432545DA14620C9  audit
```

The two-file text gate is green and the audit queue names nine readouts.  This
does **not** close f2: the exact read carriers of all source contours and every
retained one-step average remain to be constructed, and the current global
`nextBackground` cannot be declared local merely because its terminal
Dirichlet operator is regional.

#### C6c.8f2b exact one-scale Ubar read carrier (2026-08-18)

`tmp/BalabanCMP99SourceUbarExactReadCarrier.draft.lean` constructs, for one
positive coarse bond, the union of precisely:

- the straight fine path generating its base coarse background; and
- `Gamma_1 ++ Gamma_2 ++ Gamma_3` for every fine site in its source block.

Every oriented edge is mapped to its positive physical coordinate.  A named
lemma proves that agreement of two configurations on that coordinate implies
agreement on the oriented edge, so reversed contours do not introduce a
second convention.  The existing `Ubar_locality` theorem then derives equality
of the literal represented Ubar values from agreement on the generated
carrier.  A family version takes a finite set of selected coarse bonds and
forms the exact `biUnion` of their read carriers.

This is deliberately **not** locality of the existing complete
`CMP99PhysicalRegionalScaleData.nextBackground`: that object evaluates every
coarse bond.  The selected-family theorem is the input required by f3 to build
a genuinely localized deviation/Ubar scale rather than relabel the global
constructor.

Current scratch hashes are

```text
ADB3422777C101CA3E4683F36A687E78E6F9E09AED61C399370BDA8CF6D36835  source
5291B2A5388140F6895C58AA41BE306B95C6978813BE1DA2B734FFBDC6BDE06B  audit
```

The pair passes the text gate and the audit queue names nine readouts.  f2
remains open at the retained-tower recursion: the selected coarse-bond family
must be propagated through every one-step average, rather than replaced by
the complete global target lattice.

#### C6c.8f2c exact one-step transported-average carrier (2026-08-18)

`tmp/BalabanCMP99SourceTransportedAverageExactReadCarrier.draft.lean`
constructs the second one-scale carrier from the actual operator target.  It
ranges over exactly the active coarse sites (those whose complete fine blocks
lie in `Omega`) and, for every fine site in such a block, includes the oriented
edges of `cmp99BlockContainedContourSystem`.  Positive physical coordinates
are again generated from those lists, rather than supplied.

Pointwise agreement on that carrier first gives equality of each literal
contour holonomy, then equality of the physical adjoint transports, and
finally equality of the complete
`cmp99SourceTransportedBlockAverageCLM`.  Neither the transport family nor the
continuous-linear operator equality is an input.

Current scratch hashes are

```text
FF03B98523AD31A8B94A7F83A028828C31D8485E46A035A32B839D97159D6829  source
7ED64DD89E6AFFECA0B3565AA4CCF5BCADDE3B61559E6F9907952460341C4F3B  audit
```

The pair passes the text gate and the audit queue names four readouts.  At
this checkpoint the remaining f2 step was sharply typed: recurse these two
generated carriers (Ubar target bonds and transported-average target sites)
along the typed `CMP99SourceActiveRegionChain`.  That recursion is now
materialized by f2d--f below.  It generates each next selected family from
the next active region and does not reuse the full global `nextBackground`
as a locality theorem.

#### C6c.8f2d retained recursive read carrier (2026-08-18)

`tmp/BalabanCMP99SourceRetainedExactReadCarrier.draft.lean` now materializes
that recursion.  The stop carrier is empty.  At a successor it is exactly

```text
transportedAverageFineReadBonds(Omega)
  union UbarFineReadBondsOfCoarseBonds(tail.retainedFineReadBonds).
```

Thus agreement at the current fine scale derives both the literal head-average
operator equality and every raw Ubar equality requested by the tail carrier.
The second conclusion is deliberately pointwise on the selected tail bonds:
the module neither constructs nor equates the complete global
`nextBackground`.

The remaining f2 gap is smaller and exact: lift each selected raw Ubar matrix
equality through the direct-deviation-budget `SUN` constructor (the proof
arguments certify membership but must not affect the value), then perform the
dependent induction proving equality of every retained `Qprime` prefix.  The
f2d pair is PRE-VALIDATION scratch only; no elaboration or oracle verdict
exists.

Current f2d scratch hashes are

```text
A139EAA5477B20F7D56CEDEF46FB1566AA12CC3E02174C6E177913BE637C1374  source
86B3F622E16B0DA07DEE435A4770B72C64172F1A29D833C05C5D1BB216219A28  audit
```

#### C6c.8f2e selected next-background locality (2026-08-18)

`tmp/BalabanCMP99SourceSelectedNextBackgroundLocality.draft.lean` implements
the first half of that remaining gap.  It proves that the direct-budget `SUN`
block coerces to the same literal raw `Ubar` formula, so its budget and
deviation proof affect only certification.  The f2b selected-family equality
then lifts to selected `SUN` blocks and finally to the positive coordinates of
the two canonical source `nextBackground` values.

The budgets and proof witnesses on the two sides may differ.  The selected
coarse-bond family is generated by f2d and no complete configuration equality
is claimed.  At this checkpoint the remaining f2 step was solely the dependent
induction that feeds this selected equality to the tail and composes the equal
head average with the equal tail `Qprime`; f2f below now materializes that
induction.  The f2e pair is PRE-VALIDATION scratch only; no elaboration or
oracle verdict exists.

Current f2e scratch hashes are

```text
AB8A09BE7E31A936B4D9AA89B0133FDD871EF3A2F70B34EE7DDEAE396A09AA4B  source
7F03DACA9AB36370346AE292F430005226B2825E4DAFA9A9ACDC7D737B253DEE  audit
```

#### C6c.8f2f retained Qprime locality induction (2026-08-18)

`tmp/BalabanCMP99SourceRetainedQprimeLocality.draft.lean` now writes the final
dependent induction.  Both normalized scales and every next background are
constructed internally by the literal source recursion.  At a successor, f2d
derives the head-average equality, f2e derives equality only on the tail's
selected positive bonds, and the induction hypothesis identifies the tail
`Qprime`; the two literal compositions then agree.

The theorem accepts neither a complete next-background equality nor an
operator equality.  Its two backgrounds are still globally admissible
extensions.  Removing that global premise from the Corollary-3.6 consumer is
the separate f3 localized-scale constructor, so this PRE-VALIDATION scratch
does not close or count f3.  No elaboration or oracle verdict exists for f2f.

Current f2f scratch hashes are

```text
2323ED1C7EACB00B604B9844E92528CEEFE7247FDAB53A59DEFABC29FF8FBD7E  source
719594623C1A3363C082318E5865B90A68DE77F1B30809B1CA38DCD5C6A78CF8  audit
```

#### C6c.8f3a local Ubar-deviation bound (2026-08-18)

Static inspection of
`norm_cmp99SourceUbarDeviationLogArg_le_fineRadius` shows that its global
`fine_small` premise is used only four times: on `Gamma_1`, `Gamma_2`,
`Gamma_3`, and on the straight base-coarse path.  All four lists are already
subsets of the exact f2b carrier.

`tmp/BalabanCMP99SourceUbarLocalDeviationBound.draft.lean` therefore repeats
the literal estimate with smallness restricted to that carrier.  A separate
orientation lemma transports the positive-coordinate bound to a reversed edge
using special-unitary inversion, so no hidden oriented-edge convention is
added.  The same printed radius `3*d*(M-1)+M` is retained exactly.

This is a genuine weakening of the old global premise, not a renamed
deviation hypothesis.  The remaining f3 work is to construct the complete
selected/identity coarse background and prove its global next-scale radius,
then recurse it.  The f3a pair is PRE-VALIDATION scratch only; no elaboration
or oracle verdict exists.

#### C6c.8f3b selected/identity next background (2026-08-18)

`tmp/BalabanCMP99SourceLocalizedNextBackground.draft.lean` uses f3a to build
the first genuinely localized source scale object.  On each selected positive
coarse bond it constructs the literal Ubar block from that bond's exact read
carrier; on every unselected positive bond it puts the identity.  The standard
positive-bond reconstruction supplies the negative orientations.

The output is a complete coarse gauge configuration and has the same explicit
next-scale radius on every oriented edge.  Crucially, its input premise is
smallness only on the generated selected-family carrier: no global
`fineSmall` is accepted.  The raw-Ubar coercion theorem keeps the selected
values tied to the literal source formula rather than to an arbitrary patch.

The remaining f3 endpoint is recursive packaging: at each successor choose
the tail's exact retained carrier, construct this selected/identity background
and its global next-scale certificate, and prepend the literal transported
average.  The f3b pair is PRE-VALIDATION scratch only; no elaboration or oracle
verdict exists.

#### C6c.8f3c localized weighted tower (2026-08-18)

`tmp/BalabanCMP99SourceLocalizedWeightedQprimeTower.draft.lean` performs that
recursion.  Its only initial analytic premise is smallness on
`regions.retainedFineReadBonds`.  At every successor it pulls out exactly the
tail-Ubar subcarrier, constructs the f3b selected/identity background, derives
its global next-scale radius internally, restricts that result to the tail
carrier and prepends the literal physical transported average.

The constructor contains no complete-torus `fineSmall` premise for the input
background and no caller-selected next background.  Its separate depth theorem
checks that the recursion has exactly the typed source depth.  Remaining f3
work is the comparison with the canonical global source tower on any globally
admissible extension and the retained-prefix packaging consumed downstream.
The f3c pair is PRE-VALIDATION scratch only; no elaboration or oracle verdict
exists.

#### C6c.8f3d canonical-extension comparison (2026-08-18)

`tmp/BalabanCMP99SourceLocalizedTowerCanonicalExtension.draft.lean` writes the
comparison with the canonical global source tower.  Its local background is
small only on `regions.retainedFineReadBonds`; at this intermediate theorem a
separate globally admissible extension is passed and is required to agree with
the local background only on that generated carrier.  The caller-supplied
extension is eliminated by f3e below before the source-facing endpoint.

At every successor, f2d derives the transported head-average equality and the
tail Ubar subcarrier equality.  The new selected-bond bridge reduces the f3b
localized block and the canonical direct-budget block to the same literal
raw Ubar value.  The induction hypothesis then compares the tail towers.  No
complete next-background equality, Qprime equality or exterior smallness of
the local background occurs in the interface.

Current f3d scratch hashes are

```text
D342CF65C8E0A6DB0AD5691EED3110493C369631ABCA3F57545F106D3E4DCBA1  source
7555D88DE4640BE8A45088F8C9E6CFDB782AB03FAD21E789B7172252A3DF2709  audit
```

The two-file text gate is green.  This is PRE-VALIDATION scratch only: the
proof has not been elaborated and its axioms have not been checked.  Remaining
f3 work is retained-prefix packaging for the downstream C6c.7/C6c.8 consumer.

#### C6c.8f3e internally generated retained fine extension (2026-08-18)

`tmp/BalabanCMP99SourceRetainedFineExtension.draft.lean` removes the free
global extension from f3d.  It constructs a complete physical gauge
background by copying the local positive-bond values on
`regions.retainedFineReadBonds`, inserting the identity on every other
positive bond, and using the standard inverse reconstruction on negative
orientations.  Local smallness plus `epsilon >= 0` then gives global
smallness of this extension; no exterior field or exterior estimate is an
input.

The final theorem specializes f3d to this internally generated extension.
Thus the localized tower is identified with a literal canonical source tower
without accepting an extension, a global-smallness certificate, a complete
next-background equality or a Qprime equality from the caller.

Current f3e scratch hashes are

```text
4F11A4E2B29A5BB3D835E717A224BFABA44CFE009FB2882E216314F990928F5B  source
F04CB5A0C105DCA9A515FB92ECE09DA3B5CC41B5A5743BADBB7E085516BDD403  audit
```

The two-file text gate is green.  This remains PRE-VALIDATION scratch with no
Lean elaboration or oracle evidence.  The remaining f3 boundary is now only
the finite retained-prefix package required by the downstream C6c.7/C6c.8
consumer.

#### C6c.8f3f retained localized/canonical prefixes (2026-08-18)

`tmp/BalabanCMP99SourceLocalizedRetainedTower.draft.lean` materializes the
finite retained-prefix boundary.  A private auxiliary recursion takes a local
background and a globally admissible comparison background agreeing on the
recursive carrier.  It constructs both prefix families, their depth and zero
laws, the equality of every prefix Qprime, and the two terminal identifications.
At a successor the only comparison inputs are generated by f2d/f3d: the
literal head-average equality and equality of selected next-background
coordinates.

The public source-facing constructor fixes the comparison background to the
f3e retained identity extension.  Consequently callers supply neither an
extension, a family of prefixes, a next-background equality nor a Qprime
equality.  Constructor privacy prevents unrelated prefix families from
inhabiting the interface.

Current f3f scratch hashes are

```text
2818165FE0F2779515EC524AEB1ACF947C16E361999BAC4C80E21BBFE2EBB624  source
5C410626909A2AACCB7AE484BB7E3D84FA23C9B70A6822286D307C4EC61F4DE5  audit
```

The two-file text gate is green.  This closes the planned f3 mechanism only
at the static PRE-VALIDATION level; no declaration has been elaborated and no
axiom output exists.  The next source brick is f4, deriving local near-identity
links from the literal exponential chart and the (3.35) amplitude bound.

#### C6c.8f4 retained near-identity endpoint (2026-08-18)

`BalabanCMP99Eq335PhysicalRetainedNearIdentity.draft.lean` now materializes
the local endpoint required by f3f.  Its geometric premise is the named gate
`CMP99Eq335RetainedFineReadCarrierInsideRegularCube`: both endpoints of every
positive bond in `regions.retainedFineReadBonds` lie in the source regular
cube.  This is deliberately distinct from the one-bond Laplacian collar gate;
neither carrier is silently identified with the other.

The scale factor is discharged internally:

```text
|eta| * [geometryFactor * Mlarge * alpha0 * (L^j * eta)^-1]
  = geometryFactor * Mlarge * alpha0 * (L^j)^-1
  <= alpha1.
```

Using the literal `U^u = exp(eta A)` identity, the coordinate-to-matrix norm
comparison and the existing half-unit exponential estimate yields the honest
radius `2 * alpha1`.  The only scalar input not already in the regularity
witness is `alpha1 <= 1/2`; it is a visible window, not absorbed into a new
`fineSmall` premise.  The theorem is local on the retained carrier and makes
no claim of global background smallness.

Current scratch hashes and text-gate status must be regenerated after this
addition.  The module remains PRE-VALIDATION: it has not been elaborated and
has no compiler or axiom-oracle verdict.

#### C6c.8f5a retained input package (2026-08-18)

The available finite prefix of f5 is now materialized as
`BalabanCMP99Eq335PhysicalLocalizedRetainedTower.draft.lean`.  It names the
literal transformed background selected by the source witness, inserts f4's
local bound into the private f3f recursion, and derives the terminal retained
`Qprime` equality.  The caller supplies only the typed region chain, the
source-geometric inclusion, `alpha1 <= 1/2`, and the scalar Ubar radius chain
at the explicit radius `2 * alpha1`.  It supplies no `fineSmall`, extension,
tower, prefix family or equality.

This is not the complete f5 endpoint.  The C6c.7 four-action producer remains
absent by the independent C6c.7 design audit.  Until it exists, no wrapper may
accept its four desired estimates as fields and call the result Corollary 3.6.

The exact terminal type audit of 2026-08-18 sharpens this boundary.  The four
actions have owner orientations `site -> site`, `site -> bond`, `bond -> site`
and `site -> site`, respectively, and amplitudes `[B0*ell^2, B0*ell,
B0*ell, B0]` at one common rate.  f5a supplies none of these predicates.  In
particular, the retained `Qprime` equality is an operator-dictionary input to
the later transport; it is not an action bound and does not justify a generic
adjoint bridge for the right action.
The honest boundary after f5a is therefore:

```text
source regularity/locality -> retained prefixes + terminal Qprime equality
                           -> [C6c.7 four-action producer still absent]
                           -> C6c.8d/e transport -> C6c.9 assembler.
```

#### C6c.8f5b source-region closure (2026-08-18)

The scratch pair
`BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion*.draft.lean`
now composes f2g.5 with f5a.  Its public constructor receives the printed
source-region dictionary (`head region = OmegaPrime0` and
`OmegaPrime0.sites subset regular cube`) and derives the intermediate
retained-carrier/cube premise internally before constructing the retained
prefix and terminal `Qprime` equality.

This removes `hinside` from the next public boundary, but it remains
PRE-VALIDATION and does not make f2g or f5a compiler-verified.  It constructs
no Green, no common constants and none of the four C6c.7 action predicates.
The missing continuation is unchanged:

```text
source-region dictionary -> f2g endpoint theorem -> f5a retained prefix
                         -> [C6c.7 four-action producer absent]
                         -> C6c.8d/e -> C6c.9.
```

## Acceptance gates

1. **Exact object gate.**  The transformed side is the existing literal
   canonical regional precision/Green generated from `gaugeAct u U`.  The
   original side is the uniquely generated regular-background object obtained
   by the inverse gauge transport above, with every one-step average and
   recursive background identified by theorem.  It is not a caller-chosen
   tower.  Do not demand the existing near-identity constructor on `U`, since
   its `fineSmall` premise is not part of Corollary 3.6.
2. **No arbitrary equality gate.**  No field has type `GreenU = ...`,
   `precisionU = ...` or one of the final action inequalities.
3. **Tower gate.**  Eq. (3.32) is proved for the canonical retained multiscale
   `Qprime`, not only for the already sealed one-step average.
4. **Locality gate.**  Extension of the local regularity gauge outside the
   source cube is justified by a named domain/collar locality theorem.
5. **Orientation gate.**  The fine action, coarse action and positive-bond
   action use the same source/target convention as the sealed contour theorem.
6. **Norm gate.**  The common amplitude and decay rate are unchanged because
   the actions are isometries.  No cardinality factor is introduced by
   transporting the owner-weighted bounds.
7. **Full-source gate.**  If the public claim cites Corollary 3.6, the three
   source operator families are accounted for.  A terminal four-action
   projection may be exposed separately, but it must not be described as the
   whole corollary.

## Negative inventory

- The existing Ubar covariance theorem is necessary for the tower induction
  but is not covariance of the Green.
- The existing one-scale block-average covariance theorem is Eq.-(3.32) at one
  scale only.
- Self-adjointness does not replace the right-action/orientation proof.
- A global gauge transform chosen freely is not the CMP99 (3.35) regularity
  theorem; the local cube and its scalar gate must remain visible.
- Near-identity estimates for `gaugeAct u U` do not identify the Green of `U`
  without the exact precision/inverse intertwiners.
- `fineSmall (gaugeAct u U)` does not imply `fineSmall U`; unitary gauge
  transformation preserves norms of Lie-algebra fibres, not distance of link
  matrices from the identity.  Requiring both would silently shrink the
  regularity domain.

## Counter discipline

C6c.8 is a source dictionary below C6c.9.  This static design does not move
`20/41`, does not attain window 15 and does not inhabit `TermSource`.
