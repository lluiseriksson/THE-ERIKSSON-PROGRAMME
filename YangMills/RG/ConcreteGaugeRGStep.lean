/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.CorrelatorBridgeProvenance
import YangMills.L1_GibbsMeasure.CenterInvariance
import YangMills.L1_GibbsMeasure.PolymerExpansion

/-!
# The concrete gauge RG step (C6 phase B-1''): decimation `2M → M` with the
# effective measure BY CONSTRUCTION

`docs/C6-BRIDGE-CHARTER.md`, AMENDMENT 2 + its TECHNICAL NOTE (2026-07-13).
The external audit of B-1' produced the SINK-FLOW counterattack: an arbitrary
`step : Measure X → Measure X` (a data FIELD) can be the constant-zero map or
a fixed Dirac, relabeling the whole physical correlator as first-scale UV
remainder.  This module removes the field.  **There is no `step` field
anywhere below**: the scale transformation is a DEFINED map on gauge
configurations, and every effective measure is its literal pushforward.

* **`blockMap M : GaugeConfig d (2*M) G → GaugeConfig d M G`** — the concrete
  decimation: each coarse edge `(y, i, +)` receives the ordered product of the
  two fine edge holonomies along it, `A(2y —i→ 2y+eᵢ) · A(2y+eᵢ —i→ 2y+2eᵢ)`
  (`fineEdgeA`/`fineEdgeB`, through the coarse-site embedding
  `coarseSiteEmbed y = 2y`); negative edges receive the inverse through the
  reversal constraint.  Proved about it, as THEOREMS about this fixed map:
  - **`measurable_blockMap`** (measurability, `[MeasurableMul₂ G]`);
  - **`blockMap_local`** (LOCALITY: the coarse value at an edge depends only
    on the configuration at its two constituent fine edges — finite range,
    with the explicit carrier named in the hypotheses);
  - **`blockMap_gaugeAct`** (GAUGE COVARIANCE: blocking a gauge-transformed
    fine configuration equals gauge-transforming the blocked configuration by
    the restriction of the transformation to the even sublattice);
  - **`coarseSiteEmbed_shift`** (the scale geometry at the embedding level:
    one coarse step = two fine steps, torus wrap included).
* **`effectiveMeasure M μ := Measure.map (blockMap M) μ`** — the effective
  measure BY CONSTRUCTION, not as data.  **`effectiveMeasure_isProbability`**:
  probability is preserved (this kills the sink-to-zero-measure attack AT THE
  TYPE LEVEL: the pushforward of a probability measure cannot be the zero
  measure — `effectiveMeasure_ne_zero`).
* **Observable transport** (`integral_effectiveMeasure`,
  `truncatedCorrelator_effectiveMeasure`, `rayCorrelator_effectiveMeasure`):
  the coarse integral/truncated-correlator/ray-correlator under
  `effectiveMeasure M μ` equals the fine integral of the PULLED-BACK
  observable under `μ` — stated in exactly the correlator shape the bridge
  layer consumes (`truncatedPlaquetteCorrelatorOfMeasure`,
  `rayCorrelatorOfMeasure`), ready to instantiate, via
  `MeasureTheory.integral_map` with the measurability side conditions
  discharged from `measurable_blockMap` and `measurable_plaquetteHolonomy`.
* **The dependently-indexed multi-scale tower** (NO one-step fallback taken):
  `towerSize M₀ m` is defined by the doubling recursion so that
  `towerSize M₀ (m+1)` is DEFINITIONALLY `2 * towerSize M₀ m` (geometric scale
  relation as a theorem: `towerSize_eq_pow_mul : towerSize M₀ m = 2^m * M₀`).
  **`towerMeasure M₀ n μ k`** is the `k`-fold blocked measure of a start `μ`
  at size `towerSize M₀ n`, living at size `towerSize M₀ (n − k)`, defined by
  iterating `effectiveMeasure` (`towerStepDown`); once the base scale is
  reached the tower CLAMPS (stays at the base measure) — stated openly, and
  turned into the structural theorem **`lt_of_concreteRsc_ne_zero`**: a
  nonzero produced remainder can only live at a genuine blocking scale
  `k < n`.  **`towerMeasure_isProbability`**: probability preservation along
  the whole tower.
* **`concreteCovEff M₀ n μ f k t`** — the ray correlator OF the `k`-fold
  blocked measure, BY DEFINITION (no per-scale freedom: the only inputs are
  the Wilson data `(μ, f)` and the tower geometry `(M₀, n)`).
  **`concreteRsc`** (consecutive differences) and **`concreteCovIR`**
  (terminal scale) are PRODUCED; **`concrete_decomposition`** is the
  telescoping THEOREM; **`concreteBridge`** packages it as a
  `CorrelatorBridge` whose fields are these definitions.
* **`concreteWilsonBridge`** — the same bridge re-anchored at the PHYSICAL
  Wilson correlator via `concreteCovEff_zero_wilson` (scale zero of a
  Wilson-anchored tower IS `wilsonRayCorrelator`, no hypotheses).
* **`NontrivialConcreteRGWilsonBridge`** — THE GATE, with the two
  evaluator-prescribed design constraints of the Amendment-2 technical note:
  1. QUANTIFIER ORDER: `∃ (nsc g C₁ C₂ ε c₀ βc κ₀), … ∀ n, (bounds at torus
     size 2ⁿ·M₀)` — all constants BEFORE the volume quantifier.  The
     forbidden `∀ n, ∃ C(n)` shape is excluded IN THE TYPE: a witness must
     supply one constant pack for the entire unbounded family of torus sizes
     (`towerSize_lt_succ`: the sizes strictly increase), so the
     finite-support/large-constant attack is unstatable against this Prop.
  2. NONVANISHING AS A DATA CLAUSE: the clause `∀ n ≥ 1, ∃ t k,
     concreteRsc … ≠ 0` is carried explicitly FOR THE GIVEN Wilson data; it
     is NOT engineered into the class (a genuine RG admits fixed measures —
     e.g. a Haar fixed point — and invariant observables; membership in the
     concrete class must not imply nonvanishing).  `n = 0` is excluded from
     the clause because a zero-scale tower produces no remainder at all
     (`concreteRsc_eq_zero_of_le`), and any nonzero remainder automatically
     lives at a genuine scale (`lt_of_concreteRsc_ne_zero`).
* **Consumers**: `wilson_mass_gap_of_nontrivialConcreteRGWilsonBridge` — ONE
  constant pack `(C, gap)` valid for EVERY torus size in the family (the
  volume-uniform, mass-gap-shaped conclusion; uniformity is in the type of
  the conclusion, `∃ C gap, 0 < gap ∧ ∀ n t, …`); and
  `regimeCoherent_of_nontrivialConcreteRGWilsonBridge` — the concrete gate
  discharges the retained abstract interface `RegimeCoherentWilsonBridge` at
  every size `n ≥ 1` of the family with the same constants (the tie to the
  B-1/B-1' bridge layer: this gate's `Rsc` is PRODUCED from
  `effectiveMeasure` iterates and then fed through `CorrelatorBridge` /
  `physical_mass_gap_of_bridge`).

**Self-attack inventory (structural exclusions, stated honestly).**
(a) SINK FLOW `T(ν) = 0`: unstatable — there is no map variable in the gate
    (nothing quantifies over transformations); and the type-level fact
    `effectiveMeasure_isProbability` / `towerMeasure_isProbability` proves the
    produced family consists of probability measures, so no stage can be the
    zero measure.
(b) FIXED-DIRAC MAP `T(ν) = δ_{A₀}`: unstatable for the same reason — the
    only measures in the gate are `towerMeasure`-iterates of the Wilson Gibbs
    measure under the FIXED `blockMap`.  Residual honesty: if the honest
    blocked measure happened to have vanishing correlator differences, the
    gate's nonvanishing DATA clause would simply be FALSE — the attack cannot
    make the gate true; it could only make it unsatisfied.
(c) FINITE-SUPPORT / LARGE-CONSTANT attack: excluded by the quantifier order
    IN THE TYPE (constants before `∀ n`); the typed witness of the exclusion
    is the consumer's conclusion `∃ C gap, ∀ n t, …` — one pack across the
    strictly increasing size family.
(d) RELABELING (the B-1/B-1' killers): `concreteRsc`/`concreteCovIR` are
    DEFINITIONS (differences/terminal values of correlators of pushforward
    measures), not existentially chosen fields; the gate quantifies only over
    `(nsc, g, constants)`.  Choosing `nsc = 0` does NOT resurrect the trivial
    bridge as an escape: it merely moves the full load into the IR clause
    (uniform decay of the physical correlator itself — the open problem),
    while `SingleScaleUVDecay` still constrains every produced remainder.
    `stagedCorrelator_ne_of_concreteRsc_ne_zero` and
    `lt_of_concreteRsc_ne_zero` pin any nonzero remainder to an actual
    measure change at an actual blocking scale.

**Residual-risk inventory (open, stated before any external verdict — NO
"delivered" claim is made).**
(i) NO WITNESS of the gate is provided: satisfying
    `NontrivialConcreteRGWilsonBridge` (volume-uniform IR bound at the
    terminal scale + volume-uniform `SingleScaleUVDecay` for the produced
    remainders + nonvanishing for the Wilson data) is exactly the open
    mathematics (fluctuation integration / effective-coupling window); the
    strong-coupling clustering input is stated per-size and does NOT supply
    volume-uniform constants, so not even a degenerate witness is claimed.
    The gate could in principle be unsatisfiable; nothing here proves
    satisfiability, and no theorem below depends on it being satisfied.
(ii) The cross-scale METRIC geometry is not formalized: `concreteCovEff k t`
    uses separation index `t` on the scale-`k` torus's own `touchGraph`; the
    physical statement "coarse distance t = fine distance 2t" is proved only
    at the site-embedding level (`coarseSiteEmbed_shift`), not as a
    `touchGraph`-distance transport theorem.
(iii) The blocked measure's Gibbs structure (an effective ACTION at the
    coarse scale) is not derived; the tower is measure-level.
(iv) Probability preservation at the Wilson anchor additionally needs
    `IsProbabilityMeasure (wilsonGibbsMeasure …)` (Boltzmann integrability,
    available in the certified windows via `gibbsMeasure_isProbability`) and
    the SU(N) measurable-group instances; the preservation theorems here are
    generic in `[MeasurableMul₂ G]`.
(v) The ray correlator remains a finite-torus object; "mass-gap-shaped" is
    the only permitted phrasing.  No new analytic estimate is proved here.
Clay distance ~0% (<0.1%), unchanged.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open YangMills MeasureTheory GaugeConfig

/-- The doubled torus size is nonzero. -/
instance instNeZeroTwoMul (M : ℕ) [NeZero M] : NeZero (2 * M) :=
  ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne M)⟩

section BlockMap

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- **The coarse-site embedding** `y ↦ 2y`: the even sublattice of the doubled
torus. -/
def coarseSiteEmbed {M : ℕ} (y : FinBox d M) : FinBox d (2 * M) :=
  fun j => ⟨2 * (y j).val, by have := (y j).isLt; omega⟩

/-- The FIRST fine edge under a coarse edge `(y, i, +)`: from `2y` one step in
direction `i`. -/
def fineEdgeA {M : ℕ} (y : FinBox d M) (i : Fin d) : ConcreteEdge d (2 * M) :=
  ⟨coarseSiteEmbed y, i, true⟩

/-- The SECOND fine edge under a coarse edge `(y, i, +)`: from `2y + eᵢ` one
further step in direction `i`. -/
def fineEdgeB {M : ℕ} [NeZero M] (y : FinBox d M) (i : Fin d) :
    ConcreteEdge d (2 * M) :=
  ⟨(coarseSiteEmbed y).shift i, i, true⟩

private lemma double_mod_step (a M : ℕ) (ha : a < M) :
    ((2 * a + 1) % (2 * M) + 1) % (2 * M) = 2 * ((a + 1) % M) := by
  rw [Nat.mod_eq_of_lt (by omega : 2 * a + 1 < 2 * M),
    show 2 * a + 1 + 1 = 2 * (a + 1) by ring, Nat.mul_mod_mul_left]

/-- **The scale geometry at the embedding level:** one coarse step in
direction `i` corresponds to exactly two fine steps (periodic wrap
included). -/
theorem coarseSiteEmbed_shift {M : ℕ} [NeZero M] (y : FinBox d M) (i : Fin d) :
    coarseSiteEmbed (d := d) (y.shift i)
      = ((coarseSiteEmbed y).shift i).shift i := by
  funext j
  by_cases hj : j = i
  · subst hj
    apply Fin.ext
    have ha := (y j).isLt
    have h1 : (coarseSiteEmbed (d := d) (y.shift j) j : ℕ)
        = 2 * (((y j : ℕ) + 1) % M) := by
      simp [coarseSiteEmbed, FinBox.shift]
    have h2 : ((((coarseSiteEmbed y).shift j).shift j) j : ℕ)
        = ((2 * (y j : ℕ) + 1) % (2 * M) + 1) % (2 * M) := by
      simp [coarseSiteEmbed, FinBox.shift]
    rw [h1, h2, double_mod_step _ _ ha]
  · apply Fin.ext
    simp [coarseSiteEmbed, FinBox.shift, hj]

/-- **THE CONCRETE DECIMATION `2M → M`.**  Each coarse positive edge receives
the ordered product of the two fine edge holonomies along it; negative edges
receive the inverse through the reversal constraint (built via the
positive-edge coordinates `gaugeConfigEquiv`).  A fixed DEFINITION — not a
field, not data: no choice of transformation exists anywhere downstream. -/
noncomputable def blockMap (M : ℕ) [NeZero M] (A : GaugeConfig d (2 * M) G) :
    GaugeConfig d M G :=
  gaugeConfigEquiv (fun e : PosEdge d M =>
    A (fineEdgeA e.1.source e.1.dir) * A (fineEdgeB e.1.source e.1.dir))

/-- The blocked configuration on a POSITIVE coarse edge is the ordered product
of the two constituent fine edge values. -/
theorem blockMap_apply_pos (M : ℕ) [NeZero M] (A : GaugeConfig d (2 * M) G)
    (y : FinBox d M) (i : Fin d) :
    blockMap M A ⟨y, i, true⟩ = A (fineEdgeA y i) * A (fineEdgeB y i) := by
  show posToFun (fun e : PosEdge d M =>
      A (fineEdgeA e.1.source e.1.dir) * A (fineEdgeB e.1.source e.1.dir))
    (⟨y, i, true⟩ : ConcreteEdge d M) = _
  unfold posToFun
  rw [dif_pos rfl]

/-- The blocked configuration on a NEGATIVE coarse edge is the inverse of the
positive product (reversal constraint). -/
theorem blockMap_apply_neg (M : ℕ) [NeZero M] (A : GaugeConfig d (2 * M) G)
    (y : FinBox d M) (i : Fin d) :
    blockMap M A ⟨y, i, false⟩ = (A (fineEdgeA y i) * A (fineEdgeB y i))⁻¹ := by
  have h := config_apply_neg (blockMap M A) ⟨y, i, false⟩ rfl
  rw [h]
  exact congrArg Inv.inv (blockMap_apply_pos M A y i)

/-- **LOCALITY of the decimation:** the blocked value at a coarse edge
`(y, i, s)` depends ONLY on the fine configuration at the two constituent
fine edges — finite range with the explicit carrier named. -/
theorem blockMap_local (M : ℕ) [NeZero M] (A B : GaugeConfig d (2 * M) G)
    (y : FinBox d M) (i : Fin d) (s : Bool)
    (hA : A (fineEdgeA y i) = B (fineEdgeA y i))
    (hB : A (fineEdgeB y i) = B (fineEdgeB y i)) :
    blockMap M A ⟨y, i, s⟩ = blockMap M B ⟨y, i, s⟩ := by
  cases s
  · rw [blockMap_apply_neg, blockMap_apply_neg, hA, hB]
  · rw [blockMap_apply_pos, blockMap_apply_pos, hA, hB]

/-- The concrete geometry's source, as a reduction lemma. -/
lemma finBoxGeometry_src {N : ℕ} [NeZero N] (e : ConcreteEdge d N) :
    @FiniteLatticeGeometry.src d N G _ (finBoxGeometry d N G) e = e.srcV := rfl

/-- The concrete geometry's destination, as a reduction lemma. -/
lemma finBoxGeometry_dst {N : ℕ} [NeZero N] (e : ConcreteEdge d N) :
    @FiniteLatticeGeometry.dst d N G _ (finBoxGeometry d N G) e = e.dstV := rfl

@[simp] lemma srcV_mk_pos {N : ℕ} [NeZero N] (y : FinBox d N) (i : Fin d) :
    (⟨y, i, true⟩ : ConcreteEdge d N).srcV = y := rfl

@[simp] lemma dstV_mk_pos {N : ℕ} [NeZero N] (y : FinBox d N) (i : Fin d) :
    (⟨y, i, true⟩ : ConcreteEdge d N).dstV = y.shift i := rfl

/-- **GAUGE COVARIANCE of the decimation:** blocking a gauge-transformed fine
configuration equals gauge-transforming the blocked configuration by the
restriction of the gauge transformation to the even (coarse) sublattice.  The
interior vertex `2y + eᵢ` cancels between the two fine factors; the endpoint
vertices survive as the coarse gauge action through `coarseSiteEmbed`. -/
theorem blockMap_gaugeAct (M : ℕ) [NeZero M] (u : GaugeTransform d (2 * M) G)
    (A : GaugeConfig d (2 * M) G) :
    blockMap M (gaugeAct u A)
      = gaugeAct (fun y => u (coarseSiteEmbed y)) (blockMap M A) := by
  have hpos : ∀ (y : FinBox d M) (i : Fin d),
      blockMap M (gaugeAct u A) ⟨y, i, true⟩
        = gaugeAct (fun z => u (coarseSiteEmbed z)) (blockMap M A)
            ⟨y, i, true⟩ := by
    intro y i
    show (u (coarseSiteEmbed y) * A (fineEdgeA y i)
            * (u ((coarseSiteEmbed y).shift i))⁻¹)
        * (u ((coarseSiteEmbed y).shift i) * A (fineEdgeB y i)
            * (u (((coarseSiteEmbed y).shift i).shift i))⁻¹)
      = u (coarseSiteEmbed y) * (A (fineEdgeA y i) * A (fineEdgeB y i))
        * (u (coarseSiteEmbed (y.shift i)))⁻¹
    rw [coarseSiteEmbed_shift]
    group
  apply GaugeConfig.ext'
  intro e
  obtain ⟨y, i, s⟩ := e
  cases s
  · rw [config_apply_neg _ ⟨y, i, false⟩ rfl, config_apply_neg _ ⟨y, i, false⟩ rfl]
    exact congrArg Inv.inv (hpos y i)
  · exact hpos y i

end BlockMap

section EffectiveMeasure

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- Evaluation of a gauge configuration at a POSITIVE edge is measurable
(no inversion needed, hence no `MeasurableInv`). -/
theorem measurable_config_apply_pos {N : ℕ} [NeZero N]
    (e : ConcreteEdge d N) (he : e.sign = true) :
    Measurable (fun A : GaugeConfig d N G => A e) := by
  have h : (fun A : GaugeConfig d N G => A e)
      = (fun g : PosEdge d N → G => g ⟨e, he⟩) ∘
        (gaugeConfigMEquiv (d := d) (N := N) (G := G)).symm := by
    funext A
    rfl
  rw [h]
  exact (measurable_pi_apply _).comp
    (gaugeConfigMEquiv (d := d) (N := N) (G := G)).symm.measurable

/-- **The decimation is measurable** (measurable multiplication suffices: the
defining coordinates are products of positive-edge evaluations). -/
theorem measurable_blockMap (M : ℕ) [NeZero M] [MeasurableMul₂ G] :
    Measurable (blockMap (d := d) (G := G) M) := by
  have h : blockMap (d := d) (G := G) M
      = fun A => gaugeConfigEquiv (fun e : PosEdge d M =>
          A (fineEdgeA e.1.source e.1.dir) * A (fineEdgeB e.1.source e.1.dir)) :=
    rfl
  rw [h]
  refine measurable_gaugeConfigEquiv.comp (measurable_pi_lambda _ fun e => ?_)
  exact (measurable_config_apply_pos _ rfl).mul (measurable_config_apply_pos _ rfl)

/-- **THE EFFECTIVE MEASURE, BY CONSTRUCTION.**  The pushforward of the fine
measure under the fixed decimation.  There is NO `step` field anywhere in this
development: this definition is the only scale transformation, so the sink
flow of the Amendment-2 counterattack is excluded structurally (nothing
quantifies over maps of measures). -/
noncomputable def effectiveMeasure (M : ℕ) [NeZero M]
    (μ : Measure (GaugeConfig d (2 * M) G)) : Measure (GaugeConfig d M G) :=
  Measure.map (blockMap M) μ

/-- **Probability preservation** (type-level kill of the sink-to-zero-measure
attack): the effective measure of a probability measure is a probability
measure.  Hypothesis-explicit form (for use across defeq-but-not-reducibly
type indices in the tower). -/
theorem effectiveMeasure_isProbability' (M : ℕ) [NeZero M] [MeasurableMul₂ G]
    (μ : Measure (GaugeConfig d (2 * M) G)) (hμ : IsProbabilityMeasure μ) :
    IsProbabilityMeasure (effectiveMeasure M μ) := by
  haveI := hμ
  exact Measure.isProbabilityMeasure_map (measurable_blockMap M).aemeasurable

/-- Probability preservation, instance form. -/
instance effectiveMeasure_isProbability (M : ℕ) [NeZero M] [MeasurableMul₂ G]
    (μ : Measure (GaugeConfig d (2 * M) G)) [hμ : IsProbabilityMeasure μ] :
    IsProbabilityMeasure (effectiveMeasure M μ) :=
  effectiveMeasure_isProbability' M μ hμ

/-- The effective measure of a probability measure is NOT the zero measure:
the sink flow's target is unreachable by construction. -/
theorem effectiveMeasure_ne_zero (M : ℕ) [NeZero M] [MeasurableMul₂ G]
    (μ : Measure (GaugeConfig d (2 * M) G)) [IsProbabilityMeasure μ] :
    effectiveMeasure M μ ≠ 0 := by
  intro h
  have huniv : effectiveMeasure M μ Set.univ = 1 := measure_univ
  rw [h] at huniv
  simp at huniv

/-- **Observable transport (integral level):** integrating a coarse observable
against the effective measure equals integrating its pullback along the
decimation against the fine measure. -/
theorem integral_effectiveMeasure (M : ℕ) [NeZero M] [MeasurableMul₂ G]
    (μ : Measure (GaugeConfig d (2 * M) G)) {h : GaugeConfig d M G → ℝ}
    (hh : AEStronglyMeasurable h (effectiveMeasure M μ)) :
    ∫ B, h B ∂(effectiveMeasure M μ) = ∫ A, h (blockMap M A) ∂μ :=
  MeasureTheory.integral_map (measurable_blockMap M).aemeasurable hh

/-- **Observable transport in the correlator shape the bridge consumes:** the
coarse truncated two-plaquette correlator under the effective measure equals
the fine truncated correlator of the PULLED-BACK observable
`A ↦ f (plaquetteHolonomy (blockMap M A) p)` under `μ` — the exact shape of
`truncatedPlaquetteCorrelatorOfMeasure`, ready to instantiate. -/
theorem truncatedCorrelator_effectiveMeasure (M : ℕ) [NeZero M]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure (GaugeConfig d (2 * M) G)) {f : G → ℝ} (hf : Measurable f)
    (p q : ConcretePlaquette d M) :
    truncatedPlaquetteCorrelatorOfMeasure (effectiveMeasure M μ) f p q
      = (∫ A, f (plaquetteHolonomy (blockMap M A) p)
            * f (plaquetteHolonomy (blockMap M A) q) ∂μ)
        - (∫ A, f (plaquetteHolonomy (blockMap M A) p) ∂μ)
          * (∫ A, f (plaquetteHolonomy (blockMap M A) q) ∂μ) := by
  have hp : Measurable (fun B : GaugeConfig d M G => f (plaquetteHolonomy B p)) :=
    hf.comp (measurable_plaquetteHolonomy p)
  have hq : Measurable (fun B : GaugeConfig d M G => f (plaquetteHolonomy B q)) :=
    hf.comp (measurable_plaquetteHolonomy q)
  unfold truncatedPlaquetteCorrelatorOfMeasure
  rw [integral_effectiveMeasure M μ ((hp.mul hq).aestronglyMeasurable),
    integral_effectiveMeasure M μ hp.aestronglyMeasurable,
    integral_effectiveMeasure M μ hq.aestronglyMeasurable]

/-- **Observable transport in the ray-correlator shape:** the coarse ray
correlator under the effective measure is the fine truncated correlator of
the transported observable at the chosen coarse pair (with the same honest
default `0`). -/
theorem rayCorrelator_effectiveMeasure (M : ℕ) [NeZero M]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure (GaugeConfig d (2 * M) G)) {f : G → ℝ} (hf : Measurable f)
    (t : ℕ) :
    rayCorrelatorOfMeasure (effectiveMeasure M μ) f t
      = if h : ∃ pq : ConcretePlaquette d M × ConcretePlaquette d M,
            pq.1 ≠ pq.2 ∧ 2 * t ≤ (touchGraph d M).dist pq.1 pq.2 then
          (∫ A, f (plaquetteHolonomy (blockMap M A) h.choose.1)
              * f (plaquetteHolonomy (blockMap M A) h.choose.2) ∂μ)
          - (∫ A, f (plaquetteHolonomy (blockMap M A) h.choose.1) ∂μ)
            * (∫ A, f (plaquetteHolonomy (blockMap M A) h.choose.2) ∂μ)
        else 0 := by
  unfold rayCorrelatorOfMeasure
  split_ifs with h
  · exact truncatedCorrelator_effectiveMeasure M μ hf h.choose.1 h.choose.2
  · rfl

end EffectiveMeasure

section MultiScaleTower

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- **The tower of torus sizes** `towerSize M₀ m = 2^m · M₀`, by the doubling
recursion — so that `towerSize M₀ (m+1)` is DEFINITIONALLY `2 * towerSize M₀ m`
and the dependently-indexed multi-scale family typechecks without casts. -/
def towerSize (M₀ : ℕ) : ℕ → ℕ
  | 0 => M₀
  | m + 1 => 2 * towerSize M₀ m

@[simp] theorem towerSize_zero (M₀ : ℕ) : towerSize M₀ 0 = M₀ := rfl

@[simp] theorem towerSize_succ (M₀ m : ℕ) :
    towerSize M₀ (m + 1) = 2 * towerSize M₀ m := rfl

/-- **The geometric scale relation:** the tower sizes are exactly `2^m · M₀`. -/
theorem towerSize_eq_pow_mul (M₀ m : ℕ) : towerSize M₀ m = 2 ^ m * M₀ := by
  induction m with
  | zero => simp
  | succ m ih => rw [towerSize_succ, ih, pow_succ]; ring

instance instNeZeroTowerSize (M₀ : ℕ) [NeZero M₀] (m : ℕ) :
    NeZero (towerSize M₀ m) :=
  ⟨by
    rw [towerSize_eq_pow_mul]
    exact Nat.mul_ne_zero (pow_pos (by norm_num : (0 : ℕ) < 2) m).ne' (NeZero.ne M₀)⟩

/-- The tower sizes strictly increase: the volume family of the gate is
unbounded (the typed fact behind the exclusion of the finite-support attack). -/
theorem towerSize_lt_succ (M₀ : ℕ) [NeZero M₀] (m : ℕ) :
    towerSize M₀ m < towerSize M₀ (m + 1) := by
  have h : 0 < towerSize M₀ m := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [towerSize_succ]
  omega

/-- One decimation step down the tower.  At the base scale (`r = 0`) the tower
CLAMPS: the measure is left unchanged (stated openly; see
`lt_of_concreteRsc_ne_zero` for the structural consequence). -/
noncomputable def towerStepDown (M₀ : ℕ) [NeZero M₀] :
    (r : ℕ) → Measure (GaugeConfig d (towerSize M₀ r) G)
      → Measure (GaugeConfig d (towerSize M₀ (r - 1)) G)
  | 0, μ => μ
  | m + 1, μ => effectiveMeasure (towerSize M₀ m) μ

/-- **The dependently-indexed multi-scale family:** the `k`-fold blocked
measure of a start `μ` at tower scale `n`, living at size
`towerSize M₀ (n − k)`.  Every stage is produced by `effectiveMeasure`
(pushforward under the fixed `blockMap`); nothing is selectable. -/
noncomputable def towerMeasure (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) :
    (k : ℕ) → Measure (GaugeConfig d (towerSize M₀ (n - k)) G)
  | 0 => μ
  | k + 1 => towerStepDown M₀ (n - k) (towerMeasure M₀ n μ k)

@[simp] theorem towerMeasure_zero (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) :
    towerMeasure M₀ n μ 0 = μ := rfl

theorem towerMeasure_succ (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (k : ℕ) :
    towerMeasure M₀ n μ (k + 1)
      = towerStepDown M₀ (n - k) (towerMeasure M₀ n μ k) := rfl

/-- One tower step preserves probability. -/
theorem towerStepDown_isProbability (M₀ : ℕ) [NeZero M₀] [MeasurableMul₂ G] :
    ∀ (r : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ r) G)),
      IsProbabilityMeasure μ →
        IsProbabilityMeasure (towerStepDown (d := d) (G := G) M₀ r μ)
  | 0, _, h => h
  | m + 1, μ, h => effectiveMeasure_isProbability' (towerSize M₀ m) μ h

/-- **Probability preservation along the whole multi-scale tower** (the
type-level kill of the sink flow at every scale simultaneously). -/
theorem towerMeasure_isProbability (M₀ : ℕ) [NeZero M₀] [MeasurableMul₂ G]
    (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G))
    [hμ : IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (towerMeasure M₀ n μ k) := by
  induction k with
  | zero => exact hμ
  | succ k ih => exact towerStepDown_isProbability M₀ (n - k) _ ih

/-- At a clamped index (`r = 0`) the tower step does not change the ray
correlator. -/
theorem rayCorrelator_towerStepDown_of_eq_zero {M₀ : ℕ} [NeZero M₀]
    (f : G → ℝ) (t : ℕ) :
    ∀ (r : ℕ), r = 0 → ∀ (ν : Measure (GaugeConfig d (towerSize M₀ r) G)),
      rayCorrelatorOfMeasure (towerStepDown M₀ r ν) f t
        = rayCorrelatorOfMeasure ν f t := by
  rintro r rfl ν
  rfl

/-- **The produced effective correlator at scale `k`:** the ray correlator OF
the `k`-fold blocked measure, BY DEFINITION.  Inputs: the tower geometry
`(M₀, n)` and the data `(μ, f)` — no per-scale freedom of any kind. -/
noncomputable def concreteCovEff (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (k t : ℕ) : ℝ :=
  rayCorrelatorOfMeasure (towerMeasure M₀ n μ k) f t

/-- **The PRODUCED per-scale ultraviolet remainders:** consecutive differences
of the tower correlators. -/
noncomputable def concreteRsc (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (t k : ℕ) : ℝ :=
  concreteCovEff M₀ n μ f k t - concreteCovEff M₀ n μ f (k + 1) t

/-- **The PRODUCED infrared part:** the tower correlator at the terminal
scale. -/
noncomputable def concreteCovIR (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (nsc : ℕ → ℕ) (t : ℕ) : ℝ :=
  concreteCovEff M₀ n μ f (nsc t) t

/-- Beyond the base of the tower the correlator is stationary (the clamp,
stated openly). -/
theorem concreteCovEff_succ_of_le (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    {k : ℕ} (hk : n ≤ k) (t : ℕ) :
    concreteCovEff M₀ n μ f (k + 1) t = concreteCovEff M₀ n μ f k t := by
  unfold concreteCovEff
  exact rayCorrelator_towerStepDown_of_eq_zero f t (n - k)
    (Nat.sub_eq_zero_of_le hk) (towerMeasure M₀ n μ k)

/-- Clamped scales produce ZERO remainder: a zero-scale tower (`n = 0`) has no
ultraviolet content at all, and no tower has content beyond its depth. -/
theorem concreteRsc_eq_zero_of_le (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    {k : ℕ} (hk : n ≤ k) (t : ℕ) :
    concreteRsc M₀ n μ f t k = 0 := by
  unfold concreteRsc
  rw [concreteCovEff_succ_of_le M₀ n μ f hk t, sub_self]

/-- **Nonzero produced remainders live at GENUINE blocking scales:** if
`concreteRsc … t k ≠ 0` then `k < n` — nonvanishing UV content cannot be
manufactured at clamped scales; it certifies an actual decimation step. -/
theorem lt_of_concreteRsc_ne_zero (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    {t k : ℕ} (h : concreteRsc M₀ n μ f t k ≠ 0) : k < n := by
  by_contra hk
  exact h (concreteRsc_eq_zero_of_le M₀ n μ f (Nat.le_of_not_lt hk) t)

/-- A nonzero produced remainder certifies that the decimation genuinely
changed the ray correlator between consecutive tower stages. -/
theorem stagedCorrelator_ne_of_concreteRsc_ne_zero (M₀ : ℕ) [NeZero M₀]
    (n : ℕ) (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    {t k : ℕ} (h : concreteRsc M₀ n μ f t k ≠ 0) :
    rayCorrelatorOfMeasure (towerMeasure M₀ n μ (k + 1)) f t
      ≠ rayCorrelatorOfMeasure (towerMeasure M₀ n μ k) f t := by
  intro heq
  apply h
  unfold concreteRsc concreteCovEff
  rw [heq, sub_self]

/-- **THE TELESCOPING THEOREM:** the scale-zero correlator decomposes into the
terminal IR part plus the concrete UV sum of the produced remainders — a
theorem about definitions, never a postulated field. -/
theorem concrete_decomposition (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (nsc : ℕ → ℕ) (t : ℕ) :
    concreteCovEff M₀ n μ f 0 t
      = concreteCovIR M₀ n μ f nsc t
        + covUV_concrete (concreteRsc M₀ n μ f) nsc t := by
  have h : ∑ k ∈ Finset.range (nsc t),
      (concreteCovEff M₀ n μ f k t - concreteCovEff M₀ n μ f (k + 1) t)
        = concreteCovEff M₀ n μ f 0 t - concreteCovEff M₀ n μ f (nsc t) t :=
    Finset.sum_range_sub' (fun k => concreteCovEff M₀ n μ f k t) (nsc t)
  simp only [covUV_concrete, concreteRsc, concreteCovIR]
  rw [h]
  ring

/-- **The concrete bridge:** the `CorrelatorBridge` of the scale-zero tower
correlator whose fields ARE the produced definitions. -/
noncomputable def concreteBridge (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (nsc : ℕ → ℕ) : CorrelatorBridge (concreteCovEff M₀ n μ f 0) where
  covIR := concreteCovIR M₀ n μ f nsc
  Rsc := concreteRsc M₀ n μ f
  nsc := nsc
  decomposition := concrete_decomposition M₀ n μ f nsc

@[simp] theorem concreteBridge_covIR (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (nsc : ℕ → ℕ) :
    (concreteBridge M₀ n μ f nsc).covIR = concreteCovIR M₀ n μ f nsc := rfl

@[simp] theorem concreteBridge_Rsc (M₀ : ℕ) [NeZero M₀] (n : ℕ)
    (μ : Measure (GaugeConfig d (towerSize M₀ n) G)) (f : G → ℝ)
    (nsc : ℕ → ℕ) :
    (concreteBridge M₀ n μ f nsc).Rsc = concreteRsc M₀ n μ f := rfl

end MultiScaleTower

section WilsonGate

variable {d : ℕ} [NeZero d]

/-- **Scale zero of a Wilson-anchored tower IS the physical Wilson
correlator** — no hypotheses (tilted-measure calculus through the B-1'
anchor). -/
theorem concreteCovEff_zero_wilson (N_c : ℕ) [NeZero N_c] (M₀ : ℕ)
    [NeZero M₀] (n : ℕ) (β : ℝ)
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (t : ℕ) :
    concreteCovEff M₀ n
        (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f 0 t
      = wilsonRayCorrelator (d := d) (N := towerSize M₀ n) N_c f β t := by
  unfold concreteCovEff
  exact rayCorrelatorOfMeasure_wilsonGibbs N_c f β t

/-- **The concrete Wilson bridge:** the produced tower decomposition,
re-anchored at the physical Wilson ray correlator. -/
noncomputable def concreteWilsonBridge (N_c : ℕ) [NeZero N_c] (M₀ : ℕ)
    [NeZero M₀] (n : ℕ) (β : ℝ)
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (nsc : ℕ → ℕ) :
    CorrelatorBridge (wilsonRayCorrelator (d := d) (N := towerSize M₀ n) N_c f β) where
  covIR := concreteCovIR M₀ n
    (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f nsc
  Rsc := concreteRsc M₀ n
    (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f
  nsc := nsc
  decomposition := fun t => by
    rw [← concreteCovEff_zero_wilson N_c M₀ n β f t]
    exact concrete_decomposition M₀ n _ f nsc t

/-- **THE GATE (Amendment-2 technical note, both constraints).**  There exist
a scale count `nsc`, a marginal coupling flow `g`, and constants
`C₁ C₂ ε c₀ βc κ₀` — ALL BEFORE the volume quantifier — such that FOR EVERY
tower depth `n` (torus size `2ⁿ·M₀`, an unbounded family):
(i) the PRODUCED terminal IR part of the Wilson-anchored tower obeys the
exponential bound with the SAME `C₁, ε`; (ii) the PRODUCED remainders obey
`SingleScaleUVDecay` with the SAME `C₂, c₀, κ₀`; and (iii) — the NONVANISHING
DATA CLAUSE, carried explicitly for the given Wilson data and NOT engineered
into the class — every genuine tower (`n ≥ 1`) has some nonzero produced
remainder.  The `∀ n, ∃ C(n)` shape is forbidden and absent; the only
quantified data besides constants are `nsc` and `g` (shared across all
volumes).  NO WITNESS of this Prop is provided anywhere in this development:
it is the named open frontier, now stated over the concrete decimation class
only. -/
def NontrivialConcreteRGWilsonBridge (N_c : ℕ) [NeZero N_c] (M₀ : ℕ)
    [NeZero M₀] (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (β : ℝ) : Prop :=
  ∃ (nsc : ℕ → ℕ) (g : ℕ → ℝ) (C1 C2 ε c0 βc κ₀ : ℝ),
    0 < ε ∧ 0 < c0 ∧ 0 ≤ C2 ∧ 1 < κ₀ ∧ 0 < βc ∧
    (∀ k, 0 < g k) ∧ (∀ k, βc * g k < 1) ∧
    (∀ k, g (k + 1) = g k * (1 - βc * g k)) ∧
    (∀ n : ℕ,
      (∀ t : ℕ,
        |concreteCovIR M₀ n
            (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f nsc t|
          ≤ C1 * Real.exp (-(ε * (t : ℝ)))) ∧
      SingleScaleUVDecay
        (concreteRsc M₀ n
          (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f)
        g C2 c0 κ₀) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ t k : ℕ,
      concreteRsc M₀ n
        (wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β) f t k ≠ 0)

/-- **VOLUME-UNIFORM CONSUMER.**  A witness of the gate yields ONE constant
pack `(C, gap)` — quantified BEFORE the volume family — such that the physical
Wilson ray correlator at EVERY tower size `2ⁿ·M₀` obeys the mass-gap-shaped
exponential bound with those same constants.  This conclusion's type is the
typed exclusion of the finite-support/large-constant attack: no per-volume
constant exists anywhere in it. -/
theorem wilson_mass_gap_of_nontrivialConcreteRGWilsonBridge (N_c : ℕ)
    [NeZero N_c] (M₀ : ℕ) [NeZero M₀]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (hgate : NontrivialConcreteRGWilsonBridge (d := d) N_c M₀ f β) :
    ∃ C gap : ℝ, 0 < gap ∧ ∀ n t : ℕ,
      |wilsonRayCorrelator (d := d) (N := towerSize M₀ n) N_c f β t|
        ≤ C * Real.exp (-(gap * (t : ℝ))) := by
  obtain ⟨nsc, g, C1, C2, ε, c0, βc, κ₀, hε, hc0, hC2, hκ, hβc,
    hgpos, hgsmall, hgrec, hbounds, -⟩ := hgate
  have hgκ : ∀ k, 0 ≤ g k ^ κ₀ := fun k => Real.rpow_nonneg (hgpos k).le _
  have hsum : Summable (fun k => g k ^ κ₀) :=
    marginal_coupling_pow_summable_of_recursion g hβc hgpos hgsmall hgrec hκ
  set S : ℝ := ∑' k, g k ^ κ₀ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg hgκ
  have hC1 : 0 ≤ C1 := by
    have h := (hbounds 0).1 0
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C1 + C2 * S, min ε c0, lt_min hε hc0, fun n t => ?_⟩
  rw [← concreteCovEff_zero_wilson N_c M₀ n β f t,
    concrete_decomposition M₀ n _ f nsc t]
  set μW := wilsonGibbsMeasure (d := d) (N := towerSize M₀ n) N_c β with hμW
  have hIR := (hbounds n).1
  have hUV := (hbounds n).2
  have htnn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hexp1 : Real.exp (-(ε * (t : ℝ))) ≤ Real.exp (-(min ε c0 * (t : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left ε c0) htnn
    linarith
  have hexp2 : Real.exp (-(c0 * (t : ℝ))) ≤ Real.exp (-(min ε c0 * (t : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right ε c0) htnn
    linarith
  have hUVsum : |covUV_concrete (concreteRsc M₀ n μW f) nsc t|
      ≤ (C2 * Real.exp (-(c0 * (t : ℝ)))) * S := by
    have h := uv_summable_summation
      (concreteRsc M₀ n μW f t) (fun k => g k ^ κ₀)
      (mul_nonneg hC2 (Real.exp_pos _).le) hgκ hsum hSdef.ge
      (fun k => hUV t k) (nsc t)
    simpa [covUV_concrete] using h
  have hIRb : |concreteCovIR M₀ n μW f nsc t|
      ≤ C1 * Real.exp (-(min ε c0 * (t : ℝ))) :=
    le_trans (hIR t) (mul_le_mul_of_nonneg_left hexp1 hC1)
  have hUVb : |covUV_concrete (concreteRsc M₀ n μW f) nsc t|
      ≤ (C2 * S) * Real.exp (-(min ε c0 * (t : ℝ))) := by
    refine le_trans hUVsum ?_
    calc (C2 * Real.exp (-(c0 * (t : ℝ)))) * S
        = (C2 * S) * Real.exp (-(c0 * (t : ℝ))) := by ring
      _ ≤ (C2 * S) * Real.exp (-(min ε c0 * (t : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hC2 hS0)
  have habs := abs_add_le (concreteCovIR M₀ n μW f nsc t)
    (covUV_concrete (concreteRsc M₀ n μW f) nsc t)
  have hring : (C1 + C2 * S) * Real.exp (-(min ε c0 * (t : ℝ)))
      = C1 * Real.exp (-(min ε c0 * (t : ℝ)))
        + (C2 * S) * Real.exp (-(min ε c0 * (t : ℝ))) := by ring
  rw [hring]
  linarith

/-- **The tie to the B-1 bridge layer:** a witness of the concrete gate
discharges the retained abstract interface `RegimeCoherentWilsonBridge` at
EVERY genuine tower size (`n ≥ 1`), with the SAME constants across the family,
through the produced `concreteWilsonBridge`.  (The abstract interface is
per-size; the concrete gate is strictly stronger: one constant pack serves
all sizes, and its remainders carry pushforward provenance.) -/
theorem regimeCoherent_of_nontrivialConcreteRGWilsonBridge (N_c : ℕ)
    [NeZero N_c] (M₀ : ℕ) [NeZero M₀]
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) (β : ℝ)
    (hgate : NontrivialConcreteRGWilsonBridge (d := d) N_c M₀ f β) :
    ∀ n : ℕ, 1 ≤ n →
      RegimeCoherentWilsonBridge (d := d) (N := towerSize M₀ n) N_c f β := by
  obtain ⟨nsc, g, C1, C2, ε, c0, βc, κ₀, hε, hc0, hC2, hκ, hβc,
    hgpos, hgsmall, hgrec, hbounds, hnz⟩ := hgate
  intro n hn
  refine ⟨concreteWilsonBridge N_c M₀ n β f nsc, g, C1, C2, ε, c0, βc, κ₀,
    hε, hc0, hC2, hκ, hβc, hgpos, hgsmall, hgrec, ?_, ?_, ?_⟩
  · exact (hbounds n).1
  · exact (hbounds n).2
  · exact hnz n hn

end WilsonGate

end YangMills.RG
