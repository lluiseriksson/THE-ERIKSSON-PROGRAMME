# Hypothesis Frontier — THE ERIKSSON PROGRAMME

**Current as of 2026-07-02.**  This document states the honest assumption
frontier of the **verified core** (`YangMillsCore`).  Read the current
section first; the legacy section at the bottom is **archived, pre-cleanup
material that describes the EXCLUDED vacuous chain and is NOT the current
state** — it is kept only as a historical record of over-claiming and how
it was corrected.

---

## The verified core has ZERO axioms and ZERO `sorry`

`#print axioms` on **every** headline result of `YangMillsCore` returns
exactly:

```
[propext, Classical.choice, Quot.sound]
```

— Lean's three standard axioms, nothing else.  No project-specific axiom
(in particular **not** the legacy `yangMills_continuum_mass_gap`) is in
the import closure of `YangMillsCore`.  Gaps are carried as explicit
**theorem hypotheses**, never as axioms.

## The honest frontier of the M3 (lattice) mass-gap assembly

| Obligation | Status |
|---|---|
| **IR clustering bound** (`hIRbound`) | **THEOREM-FED.** Discharged by `gibbs_truncated_correlation_bound` / `sun_two_plaquette_correlator_bound` with explicit non-empty coupling windows. No carried hypothesis remains on the IR side. |
| **Strong-coupling area law** (confinement, lattice) | **THEOREM, unconditional.** Finite-volume and volume-uniform, linearized and exact-activity (`finite_volume_area_law_exp`, `normalized_exp_wilson_loop_area_law`). Carries no hypothesis. |
| **UV single-scale bound** (§6.3 Bałaban) | **CARRIED**, and now *decomposed*. The geometric-profile conditional `lattice_mass_gap_of_cluster_and_coupling` and the marginal-coupling conditional in `RG/MarginalUVMassGap.lean` are oracle-clean; coupling/summability/kernel/Gaussian scaffolding has been theorem-fed. The remaining carried input is `hRpoly`: the concrete Yang-Mills cluster-expansion-with-holes remainder activity bound for the actual gauge RG operator. It is a theorem hypothesis — never an axiom. |
| **Continuum limit / OS–Wightman reconstruction / continuum mass gap** (M4–M5, the actual Clay problem) | **OPEN MATHEMATICS.** Not carried, not axiomatized, not claimed. **Distance to the Clay prize: ~0% (<0.1%).** |

The UV frontier now also has a theorem-fed error-budget landing pad:
`YangMills.RG.YMActivityBudget.activity_decay_of_source_and_defects`.  It
turns a source-shaped activity plus covariance, dictionary, support, and
Jacobian defect bounds into one exponential activity bound with summed
amplitude and minimum decay rate.  The UV-facing adapter
`YangMills.RG.YMActivityBudget.rawYMActivityDecay_of_source_and_defects`
adds the common scale profile consumed by `RawYMActivityDecay`.  The component
estimates and the metric-to-weight comparison can now also be carried in the
named record `YMActivityErrorBudget.RawYMActivityDecomposition`, whose
projection theorem produces the same `RawYMActivityDecay` predicate.  The
record now has a theorem-fed constructor for the scale-nonnegativity field from
`∀ k, 0 ≤ g k`, but the component bounds and the metric-to-weight comparison
remain carried source/analytic obligations.  When the raw activity is
definitionally the source term plus the four defect terms and the raw weight is
the budget profile itself, the canonical constructor also discharges the exact
decomposition and profile-comparison bookkeeping fields.  Direct canonical
projections now feed `RawYMActivityDecay`, and then `SingleScaleUVDecay` only
when the exact scalar identity `Rsc = tsum Hraw`, raw/profile-weight
summability, and the weight-sum bound are supplied explicitly.  The absolute
summability of the raw-activity summand is now theorem-fed from the pointwise
raw decay estimate and the summable weight; this does not replace the
Appendix-F/H# renormalized activity theorem.  The same decomposition now
composes with the marginal-coupling mass-gap assembly via
`YMActivityErrorBudget.RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight`
and the exact-sum/profile specialization
`YMActivityErrorBudget.lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight`.
This replaces a monolithic marginal `SingleScaleUVDecay` hypothesis only after
the five component estimates, scalar identity, profile/weight summability,
weight-sum bound, IR estimate, and marginal coupling recursion are all supplied
explicitly.  The generic renormalized
with-holes scalar consumer now performs the same derived-summability step, so
downstream Appendix-F bridges no longer need a separate local
`Summable |Hsharp|` proof once the pointwise decay and summable weight are
available.  The residual with-holes layer now also names the absolute
summability consequence directly as
`summable_abs_of_clusterWithHolesActivityDecay` and
`summable_abs_of_omegaRootedClusterWithHolesActivityDecay`; these are
convergence bookkeeping theorems, not source estimates.  The Appendix-F H#
residual interfaces now expose the same convergence fact directly for rooted
total H#, finite partial H#, and total H# obtained from fixed-target summability
plus uniform partial residual bounds.  They do not discharge the residual norm
estimates themselves.  The source-majorant, geometric-profile, and closed
`cluster3` records now project rooted H# absolute summability from their
packaged residual consequences, including the integrated and CMP116 normal
forms; this removes only duplicate convergence premises, not the
majorant/source estimates.  A completed `CMP116RawSourceM3Frontier` now also
projects canonically to `PhysicalGaugeCMP116RawHsharpFrontier` and to the
raw-H# `SingleScaleUVDecay` endpoint; this is frontier-field threading only,
not a discharge of any Gaussian, source, H#, marginal-flow, or IR hypothesis.
The same completed M3 frontier now also has a direct method-style projection to
the marginal M3 assembly through the named raw-H# frontier; this is premise
plumbing only and keeps all carried fields explicit.
The weighted post-`P` source-assumption record also has a direct marginal M3
assembly method, obtained by first projecting to the raw-source M3 frontier;
all Eq. (2.29), Eq. (2.31), Appendix-F, marginal-flow, and IR obligations remain
record fields.
The resummation-source assumption record now has the same direct marginal M3
assembly method after projecting to the raw-source M3 frontier; all Eq. (2.29),
Eq. (2.31), residual-stage, Appendix-F, marginal-flow, and IR obligations remain
record fields.
The executable M3 frontier dependency graph now mirrors that projection as a
separate derived node and checks that no nonterminal derived routing node is
orphaned downstream.  It also checks that the final marginal M3 assembly node
transitively depends on all 30 frontier fields; this is an audit invariant, not
a new source estimate.

The latest source-facing UV lane also has source-only and finite-size-count
specializations.  `YangMills.RG.SourceOnlyUVDecay` handles the definitional
one-channel case `Hraw = Hsource`, while `YMActivityBudgetUV` and
`HRpolyAnimalSummability` provide finite-carrier/profile wrappers, animal
summability bridges, rooted half-budget consumers, and raw activity
finite-size-count UV routes.  Appendix-F now exposes certified
  finite-prefix/geometric-tail majorants, source-rate weighted-tree extraction,
  source-fed residual estimates, residual half-budget closure, canonical-root
  K# summability, K# smallness from the half-budget, and the source-facing
  canonical-root residual H# theorem.  P3.5--B3 now additionally composes a
  residual H# estimate with bounded-hole cardinality compression and the
  theta-shifted rate identity to discharge the local-KP pointwise `hact`
  binder and obtain the volume-uniform active-skeleton KP criterion.  The
  residual estimate and scalar KP smallness inequalities remain explicit.
  P3.5--B4 proves that this complete conditional package is jointly inhabited
  by a strictly nonzero constant activity on the minimal torus; this seals
  non-vacuity but does not identify that activity with the Yang--Mills source.
  The subsequent raw-to-KP composition removes the intermediate residual-`H#`
  caller obligation for the actual integrated Appendix-F activity: raw metric
  decay now reaches KP directly, while the raw physical estimate and its
  source-side budgets remain explicit.
  These are genuine proof obligations made smaller and better named; they are
  not proofs of the underlying Balaban/Dimock source estimates.
The 2026-06-30 source checkpoint adds the next physical-source decomposition
layer without closing the analytic frontier.  The Wilson-Hessian/Green inverse
contract is now named by `PhysicalGaugeWilsonHessianSourceDictionary`; it keeps
the CMP102 quadratic form, CMP99 Green inverse identification, normalization
scale, precision transport, and covariance transport as explicit source
fields.  The physical activity side now also exposes
`CMP119CMP122ERBSourceDecomposition`, `CMP119BLocalSourceBound`,
`CMP119BLocalActivityEstimate`, `PhysicalGaugeDimock318BLocalComponentBoundary`,
and E/R/B boundary constructors that combine CMP116 `deltaE`/local-`R`
component estimates with CMP119/CMP122 B/local and decomposition dictionaries.
These interfaces remove false monolithic assumptions; they do not prove the
component estimates, action-notation dictionary, B/local metric transport, or
the final `hRpoly` activity decay.
The 2026-07-02 source checkpoint sharpens those same open fields.  B/local now
has named dictionary frontiers for source-metric domination, rate margin,
amplitude relaxation, activity identification, Nat-metric specialization, and
source-native E/R/B boundary assembly.  Eq. (2.31) now has the definition-only
`cmp116Eq231GapCubesOfY0cStarInteriorBoundary` candidate plus its membership
lemma, giving the `Y0^{c,*}` interior-boundary path a concrete Lean object.
The source database also exposes proof-obligation cards and a hypothesis
removal queue for the highest-leverage blockers.  These changes improve the
auditability of the remaining hypotheses; they do not prove Eq. (2.31),
CMP119 Eq. (2.42), the Cammarota CMP85 theorem, activity termwise
identification, covariance-root localization, or `hRpoly`.
The same 2026-07-02 source window also starts the flow-diamagnetic UV branch
as theorem-fed producer-side scaffolding: robust marginal-coupling summability,
killed-region walk recursion, finite isometry-sum bookkeeping, block-transport
coefficient bounds, and factorial kernel convergence.  This is useful
infrastructure toward the `hRpoly` producer; it does not prove the
matrix-unitary bridge, flow-sliced measure transport, local Jacobian,
marginal extraction, or activity-decay estimate.
The 2026-07-03 Catalan/Schur checkpoint closes the finite combinatorial budget
lane: exact rooted Catalan closure, finite Catalan partial sums, convolution
support/flattening, quadratic and reset recursions, the scaled closed square-root
bound, Schur-Catalan budget transport, block-Poincare coercivity consumers, and
covariance from a Catalan-controlled physical precision defect.  The Catalan
defect estimate and physical/source identification remain explicit hypotheses,
so this does not prove the Wilson Hessian, covariance-root localization,
Appendix-F source construction, `hRpoly`, the lattice mass gap, or Clay.
The 2026-07-04 source window adds two more finite interface closures.  First,
`YangMills.KP.ActivityDomain` adopts the zero-free activity-domain interface:
KP activity domination preserves the criterion, so one KP weight controls a
closed activity polydisc and the fugacity section is a polynomial.  Second,
`YangMills.RG.Diamagnetic` now bridges concrete complex unitary matrices to
Euclidean linear isometries and instantiates the finite path-family isometry
sum bound.  These remove local adapter obligations; they do not prove the heat
kernel identity, source term, covariance/root theorem, raw activity estimate,
Wilson-flow measure decomposition, `hRpoly`, the lattice mass gap, or Clay.

### What discharging the carried UV inputs would (and would not) buy

* Discharging `hRpoly` would make the **lattice** (M3) mass gap
  unconditional through the existing conditional assembly.  `hRpoly` is the
  Dimock/Balaban cluster expansion with holes plus the fluctuation-integral
  estimate — genuine, **months-scale** constructive QFT with no Mathlib
  primitives.  The older geometric `hg` branch remains documented as the
  irrelevant-operator mechanism; the 4D *marginal* coupling side now uses the
  theorem-fed summable profile instead (see `docs/BALABAN-SOURCE-BOUNDS.md` §4).
  As of 2026-07-04, the surrounding adapters include Appendix-F/H# source-facing
  consumers, integrated second-gas KP wrappers, target-card tilt bookkeeping,
  P4 coercivity budgets, gauge-fixed precision composition, and exact
  finite-dimensional covariance from strict coercivity.  They now also include
  physical gauge cochains, a fixed-volume flat Hodge/block Poincare bridge, a
  one-dimensional harmonic classification base case, a finite-torus curl/div
  classification, source-facing covariance/root localization certificates, a
  local physical fluctuation-activity certificate, generic/CMP116 `K#`/`H#`
  and second-gas dependency wrappers, cluster-union containment facts, exact
  CMP116 local-operator support algebra, physical/CMP116 coordinate
  dictionaries, localized-root transport, dictionary-backed Gaussian/activity
  construction, canonical Gaussian integral consumers, raw-source transport
  into CMP116 `hraw`, scale-indexed raw-source H# consumers, raw-source M3
  frontier bundles, an executable M3 frontier dependency graph,
  source-assumption packaging into that frontier, the source-facing Balaban
  CMP116 theorem target, CMP116 Lemma 3 activity-only estimates, raw-source
  adapters, Eq. (2.29) consumers, Eq. (2.31) weighted `P`-stage and post-`P`
  routes, P-stage and `Z0` source-budget adapters, Eq. (2.31)
  source-membership/projected-carrier/positive-tail/interior-boundary routes,
  Gaussian source-record package constructors, residual-stage/post-`P` source
  packages, visual Eq. (2.37)/C3 citation extraction, the public `source-db`
  frontier/artifact lookup layer, the resolvent-first local SPD precision
  substrate, local-SPD root frontier packaging, dictionary root-map norm
  budgets, finite-piece root sums, finite-family physical activity consumers,
  source-only UV routes, finite-size-count and animal-summability bridges,
  Appendix-F certified-tail/source-fed residual routes, Wilson-Hessian/Green
  source dictionaries, CMP119/CMP122 E/R/B and B/local component interfaces,
  B/local metric/rate/amplitude/activity dictionary frontiers, Eq. (2.31)
  `gapCubes` candidate definitions, source-db proof-obligation cards, and
  canonical-root K# and residual H# adapters, the flow-diamagnetic
  marginal-coupling, killed-walk, block-transport, factorial-kernel
  substrate, and the Catalan majorant / Schur-budget / physical-precision
  covariance lane, finite unitary-to-isometry bridge, and KP activity-domain
  zero-free polydisc.  None of these proves the
  concrete YM source estimate.
* Even a full M3 discharge **does not** touch M4/M5.  The Clay distance
  stays ~0% (<0.1%) until the continuum limit and reconstruction exist.

Machine-checked record: `docs/VERIFICATION-LEDGER.md` (latest addenda).
Source-grounding for the carried inputs:
[`docs/BALABAN-SOURCE-BOUNDS.md`](docs/BALABAN-SOURCE-BOUNDS.md).
Adversarial attribution/provenance audit:
[`docs/SOURCE-CLAIM-AUDIT.md`](docs/SOURCE-CLAIM-AUDIT.md).

## Fleet frontier (satellite repositories, checkpoint 2026-07-04)

The satellite fleet (see `SATELLITES.md`) advanced today; this section
records what that does and does NOT change for the frontier above.

**What changed in this repository:** `YangMills/KP/ActivityDomain.lean`
adopts upstream, from the first external consumer (`lean-zero-free-regions`),
the observation that `KPCriterion` reads activities only through norms.
Consequences now proved natively here: the KP criterion is monotone under
pointwise activity domination, hence one KP weight certifies `Ξ ≠ 0` on the
whole closed activity polydisc, and the fugacity section `w ↦ Ξ(w·z)` is an
explicit polynomial.  These are elementary given KP2; their value is the
region form of the nonvanishing statement.

**What exists fleet-side (external evidence, NOT imported by this
repository — the dependency direction is satellites → mother, never the
reverse):** first zero-carried-hypothesis instances of the fleet interfaces
— the gap⇔clustering dictionary on the ferromagnetic Ising chain
(`lean-transfer-matrix`), reflection positivity of the ferromagnetic bond
with the RP ⟺ PSD-kernel characterization (`lean-os-positivity`), the
identification of the SU(2) Witten zeta with Mathlib's `riemannZeta`
(`lean-2d-yang-mills`), the discrete parabolic maximum principle with mass
conservation (`lean-ym-flow`), and a locally verified certified-interval
numerics layer whose 2D honesty-gap report quantifies the distance between
the formal `(16d+1)²σ < 1` window and physical couplings at three orders of
magnitude in `β` (`ym-lattice-numerics`).  All Lean-side session pushes are
`pending-CI` and count as nothing until their heartbeats are green.

**What did NOT change:** the M3 table above (`hRpoly` remains the carried
input), and the bottom line.  Nothing in the fleet touches the continuum
limit, OS–Wightman reconstruction, or the continuum mass gap.
**Distance to the Clay prize remains ~0% (<0.1%).**


---

<details>
<summary><b>⚠️ ARCHIVED LEGACY (pre-cleanup, v0.1–v0.30) — describes the EXCLUDED vacuous chain. NOT the current state. Historical record only.</b></summary>

> **The material below predates the 2026-05 cleanup
> (`CLEANUP_PLAN.md`, `FOUNDATIONS.md`).**  It describes the legacy
> terminal chain `L8_Terminal/ClayTheorem` and its named axiom
> `yangMills_continuum_mass_gap`, together with the vacuous target
> `clay_millennium_yangMills : ∃ m > 0` (provable by `⟨1, one_pos⟩`,
> nothing about gauge theory needed).  **All of this is EXCLUDED from
> `YangMillsCore`** — the verified core imports none of it and contains
> zero axioms.  The "frontier closed (0 remaining)" language below refers
> to that legacy *axiomatized* chain, NOT to a solved problem; it is
> exactly the kind of over-claiming the cleanup corrected.  Kept here as
> a cautionary historical record.

### Legacy terminal theorem (EXCLUDED)

```lean
-- LEGACY / EXCLUDED FROM CORE — do not cite
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys := …  -- vacuous
```

### Legacy "frontier closed" table (EXCLUDED — refers to the axiomatized chain)

The legacy audit reported "0 hypotheses remaining" only because the single
real obligation (`hContinuumMassGap` = the Clay problem itself) had been
**promoted to the named axiom** `yangMills_continuum_mass_gap`.  That is
not progress; it is assuming the conclusion.  The current core does the
opposite: it carries gaps as hypotheses and proves only what is genuinely
proved.

### Legacy weak/strong terminal split (EXCLUDED)

| Identifier | Prop | Note |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | Substantive only relative to the `yangMills_continuum_mass_gap` axiom |

Both are outside `YangMillsCore` and are scheduled for staged removal
(`CLEANUP_PLAN.md`).

*Legacy sections last meaningful at v0.30.0 (2026-03/05); superseded by
the verified-core frontier above.*

</details>
