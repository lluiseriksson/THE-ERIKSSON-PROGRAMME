# Step 8b.24 / C6c — measured regional frontier

Status: static signature audit only.  No declaration in this note has been
checked by Lean, Lake or an axiom audit.

## What C6b actually produces

C6b bounds the ambient complex operator

```text
G_flat_generated_complex ∘ Q'^*_weighted
```

on an arbitrary coarse field whose source-owner map is the identity.  Its
input carrier is

```text
FinitePiLpField (FinBox 4 (2*(K*Q))) (SUNLieComplexCoord Nc),
```

and its output is evaluated on the full source-separated fine torus after the
exact Step-7b site equivalence.  Its common coefficient is the explicit C6a
`PointSourceB0`, and its decay rate is `rho`.

The absence of a source-cardinality factor is genuine: one identity-owner
fibre contains exactly one coarse site.

## What the regional source contract requires

`CMP99Eq342SourceLocalizedGreenCertificate` has a different carrier and four
different operators.  For one active region `Omega`, it asks for

```text
G'_Omega
D_Omega G'_Omega
G'_Omega D_Omega^*
Delta_Omega G'_Omega
```

where `G'_Omega` is definitionally the canonical real inverse of the
Dirichlet compression of the literal ambient precision.  Every field is a
`FinitePiLpTypedBlockLocalizedSupBound` on arbitrary fine regional input,
with common owner metric, common positive `delta0`, common positive `B0`, and
the printed scale vector

```text
[B0*ell^2, B0*ell, B0*ell, B0].
```

## Non-definitional gaps

| C6b | regional (3.42) contract | missing producer |
|---|---|---|
| ambient full torus | active Dirichlet region | boundary/gauge dictionary |
| complex coordinate fibre | real `SUNLieCoord` PiLp | complexification/real-slice transport |
| `G Q'^*` | `G'` | full-Green endpoint; `Q'^*` cannot be erased definitionally |
| one coarse identity-owner fibre | arbitrary fine source-owner fibre | source-scale input transport, retaining the printed `ell^2` rather than a volume factor |
| value action only | value plus three derivative actions | separate Fourier/physical producers and a common-majorant proof |
| coefficient `PointSourceB0` | one positive `B0` and `delta0` for all four fields | common scalar package and positivity |

The existing `cmp99RegionalDirichletGreen` is constructed internally from
the compressed precision.  Merely restricting the ambient Green is not its
definition and no equality between those two operators is currently a sealed
input.  Likewise, `Q'^*` maps coarse fields into a special fine subspace; C6b
does not quantify all fine regional inputs.

## Compiler-visible producer inventory at `b05ef65a`

This table records declarations present in the tracked tree. It does not
promote any scratch declaration or infer a producer from a source citation.

| requested action | strongest tracked construction | exact remaining gap |
|---|---|---|
| Fourier Green value | `cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen` is the literal source-normalized Brillouin integral; its forward difference is proved internally | its identification with the generated physical `G Q'^*` is still open at this checkpoint, and it is not the unrestricted regional `G'` |
| left derivative | `cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel` and the exact forward-difference theorem produce the scalar Fourier kernel with the printed orientation | the scalar kernel is not yet transported to `D_Omega G'_Omega` on arbitrary regional fine input |
| right adjoint derivative | the Step-7.5clii/Step-8b physical chain fixes the opposite-momentum row and the exact Fourier orientation of the flat weighted adjoint `Q'^*` | this is an input-side averaging-adjoint dictionary, not a producer of `G'_Omega D_Omega^*`; the primary source produces this action later through the CMP96 Proposition 2.2 random-walk construction, not as a separate CMP89 Fourier endpoint |
| Laplacian action | the literal regional covariant Laplacian and the certificate field are defined; downstream consumers use the named field | no tracked producer of `Delta_Omega G'_Omega` was found; CMP96 (2.67) derives it together with the other actions after the local parametrix/defect expansion |

The tracked modules named `BalabanCMP89Eq248FineLatticeNormalizedFourierGreen`
and `BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative` therefore cover
only the value/left-difference Fourier layer. A repository-wide declaration
search found no corresponding normalized Fourier right-adjoint or Laplacian
Green module.  Direct visual inspection shows that this absence is expected,
not merely an implementation omission: CMP89 Lemma 2.4, equations
(2.35)--(2.37), supplies `G_j Q_j^*`, its left derivative/Hölder difference
and the coarse covariance.  CMP96 first imports the value and left derivative
in (2.43), then its Proposition 2.2/random-walk argument produces the full
list in (2.67), including `G' nabla^*` and `Delta G'`.

`BalabanCMP99SourceRegionalGreenNeumann` does not reverse this gap. It
constructs each local Dirichlet inverse internally, assembles those inverses
into a parametrix and, under the defect contraction, proves that the assembled
Neumann operator equals the ambient Green by inverse uniqueness. Its logical
direction is

```text
local Dirichlet Greens + local estimates -> ambient Green,
```

not `ambient Green bound -> each local Dirichlet Green bound`. Consequently
neither C6b nor inverse uniqueness alone can discharge the four fields of
`CMP99Eq342SourceLocalizedGreenCertificate`.

There is, however, reusable *analytic algebra* below this frontier.  The
tracked tree already defines `FinitePiLpTypedWeightedRowKernelBound`, proves
its exact same-rate composition law in
`finitePiLpTypedWeightedRowKernelBound_comp`, and instantiates the resulting
power/Neumann argument in the Eq.-(3.95) correction modules.  Those generic
lemmas are legitimate substrate for C6c.6; the Eq.-(3.95) physical operator
is not.  It is the coarse covariance correction, whereas C6c needs the fine
regional Green defect of CMP96 Proposition 2.2.

The later Eq.-(3.89) owner-row theorem also cannot be used backwards.  Its
input `C` is definitionally a
`CMP99Eq342SourceLocalizedGreenCertificate`; thus it already assumes the
four-action regional Green package that C6c is meant to produce.  It is a
downstream consumer and a useful check on coefficient/orientation
conventions, not evidence that (3.42) has a producer.

The source-facing route already recorded in the vertical map is therefore
still the required one: prove the zero-background local estimates of CMP89
Lemma 2.4, transport them through CMP89 (2.34), CMP95, CMP96 and CMP99
Corollary 3.6, and only then construct the canonical regional certificate.
The current finite-grid aliasing brick is useful input to that route, but its
success cannot by itself manufacture the two missing actions or reverse the
Neumann construction.

## Source formulas checked visually for this frontier

The relevant primary displays fix the dependency direction:

* CMP89 printed p. 582, Lemma 2.4, (2.35)--(2.37): the primitive analytic
  package is `G_j(Pi) Q_j^*`, its left derivative/Hölder difference and
  `C^(j)(Pi)`.  There is no primitive `G D*` or `Delta G` Fourier field in
  that displayed package.
* CMP96 printed p. 230, (2.40)--(2.44): the local cutoff identity consumes
  the imported value/left-derivative estimate (2.43) and produces the
  single-cell `O(M^-1)` defect.
* CMP96 printed pp. 232--234, (2.48)--(2.66): the passage from that local
  defect to the global random-walk estimate has three separate quantitative
  gates.  First, (2.48) lower-bounds the multiscale contour distance by the
  sum of its scale-normalized legs.  Second, (2.51) gives the point-supported
  defect action `O(M^-1) * exp(-delta0*d)`.  Third, Lemma 2.1, (2.60)--(2.63),
  proves a volume-free convolution bound with rate split `alpha` and requires
  the explicit separation window (2.59).  Only after these gates does
  (2.65) sum the powers of the defect and (2.66) transfer the local Green
  scale to the full Green.
* CMP96 printed p. 234, Proposition 2.2, (2.60)--(2.67): the convergent
  random-walk expansion upgrades the local inputs to the complete list
  `G'`, `nabla G'`, `G' nabla*`, both Holder actions, and `Delta G'` with
  scales `[(L^j eta)^2, L^j eta, L^j eta, ..., 1]`.

This also identifies reusable tracked substrate.  The quadratic cutoff
estimate is already present in
`BalabanCMP95SourceSignedPeriodicTensorSecondDifference`: the literal
four-dimensional signed tensor cutoff Laplacian is bounded by
`48 * secondDerivBound / M0^2`.  The earlier
`BalabanCMP96Eq240SourceSeparatedCutoffLaplacian` first-difference majorant
is algebraically valid but its sealed scale diagnostic proves it cannot be
the uniform physical producer.  C6c must reuse the quadratic estimate and
provide its exact regional/rescaling dictionary; it must not resurrect the
coarse first-difference route.

No tracked `BalabanCMP96Eq267...` producer exists.  Thus the genuinely new
analytic work after the CMP89/CMP95 input package is the typed CMP96 local
parametrix/defect and its multi-action random-walk closure, not four parallel
Fourier kernels.

## Accepted C6c chain

1. Complete the source-shaped CMP89 analytic endpoint package that is
   independent of the prefix covariance: `G_j(Pi) Q_j^*` and its left
   derivative/Hölder difference, with one scale-uniform strip radius and
   coefficient.  The current finite-grid aliasing and C6a/C6b work belong
   here.
2. Construct the literal CMP85 (2.30) prefix covariances `C^(j)`, prove the
   exact Green recurrence (2.42), and only then assemble the full CMP89
   Lemma-2.4 package, including the CMP89 Eq.-(2.37) covariance component and a
   common majorant.  Transport that package through CMP89 (2.34) and the CMP95 local
   propagator dictionaries used by CMP96.  Do not erase `Q_j^*` by
   definition; the source's renormalization identity must perform the
   conversion.
3. Formalize the CMP96 local Dirichlet parametrix and defect below
   Proposition 2.2.  Equation (2.43) supplies exactly the value and left
   derivative estimates; (2.40) and those estimates give the local
   `O(M^-1)` defect before any cell sum.
4. Sum the CMP96 random-walk/Neumann expansion with its layer bounds
   (2.60)--(2.66).  This is the producer of the full (2.67) action list,
   including the right adjoint derivative and Laplacian.  They are not to be
   fabricated as independent Fourier endpoints.
5. Upgrade the resulting actions to the fine source-owner localized
   sup-norm contract.  The value action may use the sealed exact
   `norm f <= ell^2 * finitePiLpSupNorm f` scale; no ambient-volume or
   independent owner-fibre cardinality is accepted.
6. Transport the (2.67) package through the CMP99 Corollary 3.6
   gauge/near-identity dictionary to the canonical regional Dirichlet Green.
7. Prove one `B0 > 0` and `delta0 > 0` dominate all four required actions at
   `[ell^2, ell, ell, 1]`, and only then construct
   `CMP99Eq342SourceLocalizedGreenCertificate`.

## Finite nominal brick list

The source reading bounds C6c by the following theorem-producing bricks.
Names are provisional; the conclusions, rather than the names, are the gate.

1. **C6c.1 — CMP89 analytic value/derivative endpoints.**  Assemble the
   already constructed normalized value/left-difference kernels and the
   Holder endpoint difference with one internally chosen positive
   coefficient/rate.  No estimate may be a caller field.  This prefix does
   not yet claim the full Lemma-2.4 package because its literal `C^(j)` is
   produced by C6c.2.
2. **C6c.2 — literal `C^(j)`, Eq.-(2.34), and CMP95 transport.**  Construct
   the CMP85 (2.30) covariance, prove the printed finite RG sum, assemble its
   Eq.-(2.37) decay with C6c.1 under a common majorant, and transport the
   resulting source package through the CMP95 scale dictionaries.  This is
   the only admissible place to move beyond the terminal `Q_j^*` range.
3. **C6c.3 — CMP96 (2.40) quadratic regional cutoff.**  Identify the sealed
   signed tensor second-difference coefficient with the literal rescaled
   regional cutoff and retain `48*secondDerivBound/M0^2`.  The sign dictionary
   is part of the brick: CMP96 (2.39) places `-(Delta h) lambda` inside
   `K(h)`, while the tree's positive-`D^*D` product rule exposes
   `+cutoffLaplacian` in `Delta(h phi)`, i.e. as the contribution of `-K(h)`.
   The rejected first-difference majorant is not an alternative
   implementation.  The static gate and uncompiled pair are frozen in
   `tmp/STEP8B24-C6C3-SIGN-GATE.md`.
4. **C6c.4 — CMP96 (2.43) local actions.**  Produce the value and left
   derivative bounds on an arbitrary source-owner-supported input, with no
   coordinate expansion or ambient-volume factor.  The constants must be
   chosen uniformly before the RG depth/`j` versus `j+1` branch; a family of
   per-depth witnesses is insufficient.  The exact source/terminal contract
   and the measured absence of a producer are recorded in
   `tmp/STEP8B24-C6C4-EQ243-DESIGN.md`.
5. **C6c.5 — CMP96 (2.44) local defect.**  Combine the exact three terms of
   (2.40) with C6c.4 and prove the `O(M^-1)` single-cell action before any
   overlap/layer sum.  The sign is portante: the literal physical operator is
   `first - positiveCutoffCorrection + third`.  The currently tracked
   three-species assembly uses a plus sign for the middle component, so only
   its component bounds/budget are reusable; its operator definition is not
   the C6c.5 endpoint.  C6c.5 consumes only the C6c.4 value/left-derivative
   pair, not the later right-adjoint/Laplacian fields.  The complete static
   gate is `tmp/STEP8B24-C6C5-EQ244-DESIGN.md`.
6. **C6c.6 — CMP96 (2.50), (2.60)--(2.66) random walk.**  Construct the
   Neumann/random-walk series internally from C6c.5 and prove convergence in
   the output-fixed owner-weighted supremum norm.  The older source-fixed
   `FinitePiLpTypedWeightedRowKernelBound` has the wrong orientation for
   (2.61); the correct sealed substrate is
   `FinitePiLpTypedOwnerWeightedSupKernelBound` and its convolution/power/
   Neumann algebra.  This brick must expose, rather than hide in
   one generic contraction hypothesis, (i) the contour-distance lower bound
   (2.48), (ii) the separation window (2.59), (iii) the one-step convolution
   constant `c1(alpha)` of (2.61), and (iv) the actual small parameter
   `O(M^-1)*c1(alpha)` used in (2.65).  No family of walk sums, convergence
   equality, or final exponential estimate may be supplied by the caller.
   The complete static contract is
   `tmp/STEP8B24-C6C6-EQ250-RANDOM-WALK-DESIGN.md`.
7. **C6c.7 — CMP96 (2.67) multi-action closure.**  Derive the value, left
   derivative, right adjoint derivative and Laplacian actions of the same
   generated Green, with one degraded positive rate and the printed scale
   vector.  The source actually prints six actions: the two Holder estimates
   must remain separately named even though the terminal Eq.-(3.42)
   certificate consumes only four.  The right-adjoint action has an
   orientation gate and cannot be inferred abstractly from self-adjointness;
   the Laplacian action must come from the literal precision/inverse identity.
   The exact static contract is
   `tmp/STEP8B24-C6C7-EQ267-FOUR-ACTION-DESIGN.md`.
8. **C6c.8 — CMP99 Corollary-3.6 gauge transport.**  Construct the
   source regularity witness, transform the background to its near-identity
   representative and transport C6c.7 to the literal canonical regional
   Dirichlet Green.  The tree already proves contour-holonomy covariance,
   the one-scale average intertwiner and covariance of the generated next
   background.  The missing work is the regional gauge-isometry package,
   covariant derivative/Laplacian intertwining, multiscale retained-`Qprime`
   induction, precision/Green conjugation by inverse uniqueness, and
   preservation of the action norms.  Corollary 3.6 also retains the printed
   domain-in-regular-cube and `O(1)*M*alpha0 <= alpha1` gates.  No arbitrary
   operator equality is an admissible input.  The full static contract is
   `tmp/STEP8B24-C6C8-COROLLARY36-GAUGE-DESIGN.md`.
9. **C6c.9 — physical certificate producer.**  Define the final common
   `B0` and `delta0` from the preceding explicit normalized budgets, prove
   positivity and construct `CMP99Eq342SourceLocalizedGreenCertificate`
   internally.  The tracked localized-sup predicate currently lacks the
   generic amplitude-up/rate-down weakening theorem needed by this assembly;
   that theorem is a named first substep, not a hidden `simpa`.  The uniform
   quantifier order, explicit common-majorant formula and no-renaming gates
   are frozen in `tmp/STEP8B24-C6C9-PHYSICAL-CERTIFICATE-DESIGN.md`.

The list has a declared last element and no record whose fields are the four
desired final inequalities.  Completion of a prefix is therefore not a C6c
producer and cannot move a terminal counter.

## Reuse audit against the tracked tree

| brick | reusable sealed/tracked substrate | genuinely missing result |
|---|---|---|
| C6c.1 | normalized CMP89 value integral, exact left forward difference, common strip/nonvanishing and endpoint bounds | one generated value/left-derivative/Holder endpoint package with common positive constants; it deliberately excludes the still-unconstructed literal `C^(j)` |
| C6c.2 | canonical retained `Q'_j` prefixes; source `a_j` recurrence; and a frozen 33-file P0--P5 scratch closure that constructs prefix precisions/Greens, literal CMP85 (2.30), (2.42), finite (2.43)/(2.34), and the separated carrier dictionary without caller Greens or recurrence laws | elaboration/cold audit of that exact closure; then the final CMP89 Eq.-(2.37) covariance decay/common-majorant assembly with C6c.1.  Scratch text is not a producer until compiled |
| C6c.3 | `cmp95RescaledSourcePeriodicSignedTensorCutoffLaplacianCoefficient`, its `48*secondDerivBound/M0^2` bound, and the unit-spacing `cmp99CutoffLaplacianCorrection` equality | exact sign-aware equality to the middle term *inside* `K(h)` in CMP96 (2.39)/(2.40), namely the negative of the positive correction exposed by the tree's product rule |
| C6c.4 | exact source-owner geometry and `ell^2` input conversion | arbitrary-source value/left-derivative action bounds from the generated local Green |
| C6c.5 | abstract regional commutator, inverse-sandwich and parametrix identities; the three component bounds and their separate budgets are exposed downstream | sign-correct literal operator `first - positiveCutoffCorrection + third`, its equality to the generated-precision commutator, and quantitative (2.44) action with `M^-1` before summation, derived from only the C6c.3/C6c.4 value/left-derivative pair |
| C6c.6 | `cmp99RegionalGreenNeumann` constructs the algebraic series and proves inverse uniqueness; `FinitePiLpTypedOwnerWeightedSupKernelBound` and its output-fixed convolution/power/Neumann modules provide the correctly oriented same-rate algebra | proof-carrying multiscale owner and distance (2.45)--(2.48), separation window (2.59), explicit `c0`/`c1` row sum (2.60)--(2.63), and specialization to the sign-correct *CMP96 fine regional defect* in (2.65)--(2.66); the source-fixed weighted-row predicate and a bare operator-norm contraction are both insufficient |
| C6c.7 | target action types and `[ell^2, ell, ell, 1]` scale vector are fixed by `CMP99Eq342SourceLocalizedGreenCertificate`; C6c.4 supplies the value/left local heads and C6c.6 supplies one common Neumann series | value and left actions of that series; an orientation-correct direct or block-adjoint proof for `G' D*`; a literal inverse-identity proof for `Delta G'` using the same exact CMP85 `a_j` precision/Green as C6c.2/C6c.6; one common positive amplitude/rate; and a separately named disposition of the two Holder actions printed in Proposition 2.2 |
| C6c.8 | `GaugeConfig.gaugeAct`; orthogonal `SUNAdjointModel`; exact contour-holonomy, one-scale block-average and Ubar/next-background covariance; active-region restriction/extension; coefficient-polymorphic precision/Green conjugation by inverse uniqueness | cold validation of the prepared geometric prefix; then a final specialization to the exact C6c.2/C6c.7 `a_j` precision and Green, invariance of those four action norms, and source (3.35) local-cube regularity with `O(1)*M*alpha0 <= alpha1`.  The older `cmp99SourceGeneratedPhysicalMass` specialization is auxiliary, not this endpoint |
| C6c.9 | final certificate type, its positivity projections, and the four literal canonical operator fields are present | generic amplitude-up/rate-down weakening lemma; one depth-independent common-majorant construction from the C6c.8 budgets; internal terminal constructor with no final-bound input; exact contract in `tmp/STEP8B24-C6C9-PHYSICAL-CERTIFICATE-DESIGN.md` |

The abstract Neumann file is therefore reusable algebra, but not a substitute
for the missing localized analysis.  Its theorem consumes `norm defect < 1`
in the global operator norm and concludes equality with the ambient inverse;
CMP96 Proposition 2.2 needs the finer owner-weighted estimates in order to
preserve (2.67)'s decay and scale vector.

No step may accept the four final bounds as fields of an intermediate record;
that would rename (3.42).  C6a/C6b remain useful inputs to step 1 but are not
the regional producer themselves.

### C6c.2 measured subfrontier

The exact source identity and the tree inventory are recorded in
`STEP8B24-C6C2-EQ234-DESIGN.md`.  Three tempting shortcuts are rejected:

1. `BalabanCMP99SourceRegionalCoarseCovarianceTelescope` telescopes changes
   of the spatial region `Omega`; it is not the RG-scale sum in CMP89 (2.34).
2. The generated terminal coarse covariance is one correct `C^(j)`-shaped
   ingredient, not the full propagator identity.
3. The retained stratum covariance uses one complete Green for every
   stratum, whereas (2.34) uses the prefix family `G_j`.

The retained tower already prevents caller-chosen `Q_j` prefixes.  What it
does not expose is the family of one-mass prefix precisions
`Delta_A + a_j Q_j(A)^* Q_j(A)` and their Greens on the original fine
carrier.  The complete retained precision is not a substitute: it sums all
strata simultaneously.  C6c.2 must construct the literal prefix family from
the retained `Q_j` tower and the source `a_j` recurrence, prove coercivity
internally at each prefix, and then prove the printed recurrence

```text
G_(j+1) = G_j
  + a_j^2 * (L^j eta)^(-4) * G_j Q_j^* C^(j) Q_j G_j        (2.42)
```

before summing.  The source itself says that recursive application, with
`G_1 = C^(0)`, yields (2.43), the same identity as CMP89 (2.34).  That finite
boundary is now materialized as the frozen 33-file P0--P5 scratch closure:
16 source modules, 16 sibling audits, one aggregate P3 audit and 156 public
declarations.  It passes byte/text/import/audit-coverage gates but has not
been elaborated; it therefore remains PRE-VALIDATION and cannot justify a
producer claim or a counter movement.

The index dictionary is now fixed as part of that boundary.  CMP85 uses
`a_1 = a`; Lean uses `cmp99SourceMassParameter a L 0 = a`.  Thus the printed
summand at source index `j` consumes Lean coefficient index `j - 1`, while
the operator prefix remains `Q_j`/`G_j`.  Identifying those two Nat indices
without the named shift would be a source-false but well-typed recurrence.

The prefix-coercivity frontier is also bounded.  The tracked tree has the
complete one-scale physical construction (precision, internally proved
coercivity, Green, `Q G^2 Q^dagger`, coercivity of that middle and its
inverse), the raw absorbed Poincare estimate with the literal generated
`Qprime`, and generic tower coarse-covariance algebra.  Scratch P0 now
constructs the canonical truncations and proves
`retained.towerAt r = truncated.weightedQprimeTower`; scratch P1 specializes
the raw estimate at every prefix; P2 uses the actual `a_j`.  The resulting
floor has the shape
`(1-B) * min(A^-1, a_j*C^-1)`.  The terminal theorem using
`cmp99SourceGeneratedPhysicalMass` is only an algebraic template: that mass
is a normalization quotient, not the source `a_j`.  The all-strata precision
is likewise not an admissible replacement.  These scratch proofs are the
intended solution to the former typed precursor, but remain untrusted until
their ordered focal/audits pass.  The higher physical wrapper that removes
P5's technical `fineSmall` premise is separately drafted at CMP116 level and
keeps the genuine terminal Poincare inequality visible.

### C6c.1 measured subfrontier

The primitive package is not one undifferentiated missing estimate:

1. **Value branch.**  The tracked mass-uniform complex floor removes the old
   `0 < mass` restriction, and the prepared Unit-E/Unit-F plus C0--C6b chain
   constructs the zero-mass generated `G Q'^*` value coefficient and its
   source-owner decay.  It is still scratch until promoted and validated.
2. **Left derivative branch.**  The exact pointwise identity
   `cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference` is tracked,
   and D1--D4d are now materialized as a 14-file static queue.  They derive
   differentiability and both endpoint seams from the two Green endpoints,
   run the one-coordinate/product contour telescope, construct the
   mass-uniform normalized forward-difference equality, reindex the periodic
   target seam on the exact zero-residue subtype, and reach the generated
   identity-owner localized-field estimate.  The queue has 33 proposed
   declarations with matching audit readouts and deterministic promotion
   manifest
   `E73F2CDD55D72F120FB9527BAE5F89B7AAD8B39E955D6DF9ECA3AF66D59D1D53`.
   It is wholly unelaborated and cannot be promoted before the Step-8b.23 and
   C6b cold seals.  Bounding the difference of the two final Green estimates
   and dividing by the lattice spacing remains rejected: it loses the
   cancellation that makes (2.35) scale-uniform.
3. **Holder branch.**  The phase quotient estimate is tracked, but its
   zero-mass normalized physical endpoint and operator transport are not yet
   assembled.  It is an internal CMP96 input if the multi-action proof uses
   the Holder clauses of (2.67); it is not itself a field of (3.42).  The
   source-faithful static route is now frozen in
   `tmp/STEP8B24-C6C1-HOLDER-DESIGN.md`: the visually confirmed consumer range
   `0 < alpha < 1`, physical displacement `xi*(x-x')`, every alias phase
   retained, cancellation before norms, a constructed nearest endpoint and
   one contour of the complete normalized difference, with a
   complete-polydisc nonvanishing gate.  Splitting the difference into two
   independently shifted endpoint integrals is now rejected as
   source-unfaithful: CMP89 printed p. 586 shifts the integration domain in
   the complete Eq.-(2.49) expression after assuming `|x'-y| <= |x-y|`.
   The same render fixes the two Holder
   entries of the Eq.-(2.67) scale vector as
   `(L^j*eta)^(1-alpha)*(||zeta||_alpha+|zeta|)`, with common decay rate
   `delta0/2`.  Static, unelaborated H1 and H4a--H4b drafts now construct the
   physical phase quotient, exact endpoint swap, literal nearest-endpoint
   minimum and orientation recombination.  H2 is split into a global
   complex-strip quotient and the later local-pair specialization.  No draft
   is compiler-verified or promotable yet.  The repository objects
   representing the two `zeta` quantities and the visually exact CMP95
   (1.109) local-pair carrier must still be identified before a public
   consumer signature is fixed.
4. **Coarse covariance branch.**  The tree constructs and bounds the inverse
   of the conditional middle `Q_j G_j^2 Q_j^dagger` in
   `BalabanCMP99SourceRegionalCoarseCovarianceDecay`.  That is useful proof
   substrate but is not definitionally the literal CMP85 (2.30) `C^(j)`;
   the negative identification is recorded above.  C6c.2 must first
   construct the literal inverse and then prove the CMP89 Eq.-(2.37) decay or a
   named theorem transferring an already sealed estimate to that exact
   object.  Until then the full Lemma-2.4 common-constant assembler remains
   downstream of C6c.2.

Thus the pre-C6c.2 portion of C6c.1 should be promoted as two restartable
analytic bricks (value and left-derivative/Holder).  The covariance dictionary
and common-constant assembler follow C6c.2, after the exact `C^(j)` exists.
A green value prefix alone is not Lemma 2.4.

## Counter discipline

This audit, C6a and C6b do not move `20/41`, do not attain window 15 and do not
inhabit `TermSource`.
