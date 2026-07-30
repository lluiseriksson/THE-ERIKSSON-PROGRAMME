/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit
import YangMills.L1_GibbsMeasure.WeightedGas
import YangMills.L1_GibbsMeasure.RestrictedGate
import YangMills.L1_GibbsMeasure.LocalCenteredWindow

/-!
# Genuine free-boundary Gibbs expectations

The periodic finite-volume theory sums the Wilson energy over every
plaquette of the torus.  This file supplies a second, genuinely different
finite-volume boundary condition: delete precisely the plaquettes whose
positive boundary crosses a periodic seam.  The remaining action is the
ordinary Wilson action on the free box.  Gauge variables unused by that
action remain harmless independent Haar variables.

This is a measure-theoretic construction on gauge configurations, not a
polymer-gas surrogate.  The terminal bridge to the polymer expansion is the
exact identity

`freeBoundaryPartitionFunction = weightedPartition seamDeletedWeight`.

No thermodynamic comparison is claimed in this file.  Such a comparison
must prove that the normalized marked expansions differ only through
clusters connecting the observable support to the deleted seam.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace FreeBoundary

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- A plaquette crosses the cut hyperplane if one of its two positive
coordinate steps lands on the selected first coordinate of the free box. -/
def ConcretePlaquette.CrossesCut
    (cut : FinBox d N) (p : ConcretePlaquette d N) : Prop :=
  (p.site.shift p.dir1) p.dir1 = cut p.dir1 ∨
    (p.site.shift p.dir2) p.dir2 = cut p.dir2

/-- Plaquettes retained after cutting the torus at `cut`. -/
noncomputable def plaquettesAvoidingCut (cut : FinBox d N) :
    Finset (ConcretePlaquette d N) := by
  classical
  exact Finset.univ.filter
    (fun p => ¬ ConcretePlaquette.CrossesCut cut p)

/-- A translated cut, retained as a useful comparison boundary condition. -/
def centeredCut : FinBox d N :=
  fun _ => ⟨N / 2, Nat.div_lt_self (NeZero.pos N) (by omega)⟩

/-- The standard cut at coordinate zero in every direction.  Later
thermodynamic comparisons center the observable inside this fixed free box,
so that the already banked bilateral `SiteMargin` geometry applies directly. -/
def standardCut : FinBox d N :=
  fun _ => 0

/-- Plaquettes retained by the standard free-boundary Wilson action. -/
noncomputable def freeBoundaryPlaquettes :
    Finset (ConcretePlaquette d N) :=
  plaquettesAvoidingCut (standardCut (d := d) (N := N))

@[simp]
theorem mem_freeBoundaryPlaquettes (p : ConcretePlaquette d N) :
    p ∈ freeBoundaryPlaquettes (d := d) (N := N) ↔
      ¬ ConcretePlaquette.CrossesCut
        (standardCut (d := d) (N := N)) p := by
  simp [freeBoundaryPlaquettes, plaquettesAvoidingCut]

/-- A plaquette with zero bilateral seam margin belongs to the standard
free box.  This is the exact bridge between the banked margin geometry and
the genuine deleted-seam action. -/
theorem mem_freeBoundaryPlaquettes_of_siteMargin_zero
    (p : ConcretePlaquette d N) (hp : p.SiteMargin 0) :
    p ∈ freeBoundaryPlaquettes (d := d) (N := N) := by
  rw [mem_freeBoundaryPlaquettes]
  intro hcross
  rcases hcross with hcross | hcross
  · have hupper := (hp p.dir1).2
    have hval := congrArg Fin.val hcross
    simp [standardCut, FinBox.shift, Nat.mod_eq_of_lt (by omega)] at hval
  · have hupper := (hp p.dir2).2
    have hval := congrArg Fin.val hcross
    simp [standardCut, FinBox.shift, Nat.mod_eq_of_lt (by omega)] at hval

/-- Wilson action restricted to an arbitrary finite plaquette region. -/
noncomputable def plaquetteSubsetAction
    (Q : Finset (ConcretePlaquette d N)) (pe : G → ℝ)
    (A : GaugeConfig d N G) : ℝ :=
  ∑ p ∈ Q, pe (plaquetteHolonomy A p)

/-- The free-boundary Wilson action. -/
noncomputable def freeBoundaryWilsonAction
    (pe : G → ℝ) (A : GaugeConfig d N G) : ℝ :=
  plaquetteSubsetAction (freeBoundaryPlaquettes (d := d) (N := N)) pe A

/-- Mayer weight which agrees with the periodic Wilson weight in `Q` and is
zero outside `Q`. -/
noncomputable def plaquetteSubsetWeight
    (Q : Finset (ConcretePlaquette d N)) (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) : ℝ :=
  truncWeight (fun A p => plaquetteWeight pe β A p) Q A p

/-- The seam-deleted Mayer weight representing free boundary conditions. -/
noncomputable def freeBoundaryPlaquetteWeight
    (pe : G → ℝ) (β : ℝ)
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) : ℝ :=
  plaquetteSubsetWeight
    (freeBoundaryPlaquettes (d := d) (N := N)) pe β A p

@[simp]
theorem freeBoundaryPlaquetteWeight_eq_of_mem
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G)
    {p : ConcretePlaquette d N}
    (hp : p ∈ freeBoundaryPlaquettes (d := d) (N := N)) :
    freeBoundaryPlaquetteWeight pe β A p =
      plaquetteWeight pe β A p := by
  simp [freeBoundaryPlaquetteWeight, plaquetteSubsetWeight,
    truncWeight, hp]

@[simp]
theorem freeBoundaryPlaquetteWeight_eq_zero_of_not_mem
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G)
    {p : ConcretePlaquette d N}
    (hp : p ∉ freeBoundaryPlaquettes (d := d) (N := N)) :
    freeBoundaryPlaquetteWeight pe β A p = 0 := by
  simp [freeBoundaryPlaquetteWeight, plaquetteSubsetWeight,
    truncWeight, hp]

/-- A marked monomial entirely inside the free box agrees pointwise with
the periodic Wilson monomial. -/
theorem prod_freeBoundaryPlaquetteWeight_eq_of_subset
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G)
    {S : Finset (ConcretePlaquette d N)}
    (hS : S ⊆ freeBoundaryPlaquettes (d := d) (N := N)) :
    (∏ p ∈ S, freeBoundaryPlaquetteWeight pe β A p)
      =
    ∏ p ∈ S, plaquetteWeight pe β A p := by
  apply Finset.prod_congr rfl
  intro p hp
  exact freeBoundaryPlaquetteWeight_eq_of_mem pe β A (hS hp)

/-- A marked monomial which uses a deleted plaquette vanishes pointwise. -/
theorem prod_freeBoundaryPlaquetteWeight_eq_zero_of_not_subset
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G)
    {S : Finset (ConcretePlaquette d N)}
    (hS : ¬ S ⊆ freeBoundaryPlaquettes (d := d) (N := N)) :
    (∏ p ∈ S, freeBoundaryPlaquetteWeight pe β A p) = 0 := by
  obtain ⟨p, hpS, hpQ⟩ := Finset.not_subset.mp hS
  exact Finset.prod_eq_zero hpS
    (freeBoundaryPlaquetteWeight_eq_zero_of_not_mem pe β A hpQ)

/-- A product of `1+w` with the deleted weight is exactly the ordinary
Wilson product over the intersection with the free box. -/
theorem prod_one_add_freeBoundaryPlaquetteWeight_eq_inter
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G)
    (F : Finset (ConcretePlaquette d N)) :
    (∏ p ∈ F, (1 + freeBoundaryPlaquetteWeight pe β A p))
      =
    ∏ p ∈ F ∩ freeBoundaryPlaquettes (d := d) (N := N),
      (1 + plaquetteWeight pe β A p) := by
  classical
  calc
    (∏ p ∈ F, (1 + freeBoundaryPlaquetteWeight pe β A p))
        =
      (∏ p ∈ F.filter (fun p =>
          p ∈ freeBoundaryPlaquettes (d := d) (N := N)),
        (1 + freeBoundaryPlaquetteWeight pe β A p)) := by
          symm
          apply Finset.prod_subset (Finset.filter_subset _ _)
          intro p hpF hpFilter
          have hpFree :
              p ∉ freeBoundaryPlaquettes (d := d) (N := N) := by
            intro hpFree
            exact hpFilter (Finset.mem_filter.mpr ⟨hpF, hpFree⟩)
          simp [freeBoundaryPlaquetteWeight_eq_zero_of_not_mem
            pe β A hpFree]
    _ = ∏ p ∈ F ∩ freeBoundaryPlaquettes (d := d) (N := N),
          (1 + plaquetteWeight pe β A p) := by
      apply Finset.prod_congr
      · ext p
        simp
      · intro p hp
        rw [freeBoundaryPlaquetteWeight_eq_of_mem pe β A
          (Finset.mem_inter.mp hp).2]

/-- Partition function of the genuine free-boundary action. -/
noncomputable def freeBoundaryPartitionFunction
    (μ : Measure G) (pe : G → ℝ) (β : ℝ) : ℝ :=
  ∫ A : GaugeConfig d N G,
      Real.exp (-β * freeBoundaryWilsonAction pe A)
    ∂(gaugeMeasureFrom (d := d) (N := N) μ)

/-- Gibbs probability measure for the free-boundary action. -/
noncomputable def freeBoundaryGibbsMeasure
    (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    Measure (GaugeConfig d N G) :=
  (gaugeMeasureFrom (d := d) (N := N) μ).tilted
    (fun A => -β * freeBoundaryWilsonAction pe A)

/-- Genuine finite-volume expectation with free boundary conditions. -/
noncomputable def freeBoundaryExpectation
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : GaugeConfig d N G → ℝ) : ℝ :=
  ∫ A, O A ∂(freeBoundaryGibbsMeasure μ pe β)

section Measurable

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_plaquetteSubsetAction
    (Q : Finset (ConcretePlaquette d N))
    {pe : G → ℝ} (hpe : Measurable pe) :
    Measurable (plaquetteSubsetAction Q pe) := by
  unfold plaquetteSubsetAction
  exact Finset.measurable_sum _ fun p _ =>
    hpe.comp (measurable_plaquetteHolonomy p)

theorem measurable_freeBoundaryWilsonAction
    {pe : G → ℝ} (hpe : Measurable pe) :
    Measurable (freeBoundaryWilsonAction (d := d) (N := N) pe) := by
  exact measurable_plaquetteSubsetAction
    (freeBoundaryPlaquettes (d := d) (N := N)) hpe

theorem measurable_plaquetteSubsetWeight
    (Q : Finset (ConcretePlaquette d N))
    {pe : G → ℝ} (hpe : Measurable pe) (β : ℝ)
    (p : ConcretePlaquette d N) :
    Measurable (fun A : GaugeConfig d N G =>
      plaquetteSubsetWeight Q pe β A p) := by
  classical
  unfold plaquetteSubsetWeight truncWeight
  split_ifs
  · unfold plaquetteWeight
    exact (Real.measurable_exp.comp
      ((hpe.comp (measurable_plaquetteHolonomy p)).const_mul
        (-β))).sub measurable_const
  · exact measurable_const

theorem abs_plaquetteSubsetWeight_le
    (Q : Finset (ConcretePlaquette d N))
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (A : GaugeConfig d N G) (p : ConcretePlaquette d N) :
    |plaquetteSubsetWeight Q pe β A p| ≤
      Real.exp (|β| * B) - 1 := by
  classical
  unfold plaquetteSubsetWeight truncWeight
  split_ifs
  · exact abs_plaquetteWeight_le pe β A p hpe
  · rw [abs_zero]
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β)
        (le_trans (abs_nonneg (pe 1)) (hpe 1)))

theorem integrable_freeBoundaryBoltzmann
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    Integrable
      (fun A : GaugeConfig d N G =>
        Real.exp (-β * freeBoundaryWilsonAction pe A))
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  let Q := freeBoundaryPlaquettes (d := d) (N := N)
  have hmeas :
      Measurable (fun A : GaugeConfig d N G =>
        Real.exp (-β * freeBoundaryWilsonAction pe A)) :=
    Real.measurable_exp.comp
      ((measurable_freeBoundaryWilsonAction hpe_meas).const_mul (-β))
  refine (integrable_const
    (Real.exp (|β| * B * Q.card))).mono'
      hmeas.aestronglyMeasurable ?_
  refine ae_of_all _ fun A => ?_
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  have hS : |freeBoundaryWilsonAction pe A| ≤ B * Q.card := by
    unfold freeBoundaryWilsonAction plaquetteSubsetAction
    change |∑ p ∈ Q, pe (plaquetteHolonomy A p)| ≤ _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc
      ∑ p ∈ Q, |pe (plaquetteHolonomy A p)|
          ≤ ∑ _p ∈ Q, B :=
        Finset.sum_le_sum fun p _ => hpe _
      _ = B * Q.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc
    -β * freeBoundaryWilsonAction pe A
        ≤ |(-β) * freeBoundaryWilsonAction pe A| := le_abs_self _
    _ = |β| * |freeBoundaryWilsonAction pe A| := by
      rw [abs_mul, abs_neg]
    _ ≤ |β| * (B * Q.card) :=
      mul_le_mul_of_nonneg_left hS (abs_nonneg β)
    _ = |β| * B * Q.card := by ring

/-- The free-boundary partition function is strictly positive. -/
theorem freeBoundaryPartitionFunction_pos
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    0 < freeBoundaryPartitionFunction
      (d := d) (N := N) μ pe β := by
  unfold freeBoundaryPartitionFunction
  haveI : NeZero (gaugeMeasureFrom (d := d) (N := N) μ) :=
    IsProbabilityMeasure.neZero _
  exact integral_exp_pos
    (integrable_freeBoundaryBoltzmann μ hpe_meas hpe β)

/-- The genuine free-boundary Gibbs measure is normalized. -/
theorem freeBoundaryGibbsMeasure_isProbability
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    IsProbabilityMeasure
      (freeBoundaryGibbsMeasure (d := d) (N := N) μ pe β) := by
  unfold freeBoundaryGibbsMeasure
  haveI : NeZero (gaugeMeasureFrom (d := d) (N := N) μ) :=
    IsProbabilityMeasure.neZero _
  exact isProbabilityMeasure_tilted
    (integrable_freeBoundaryBoltzmann μ hpe_meas hpe β)

end Measurable

open Classical in
/-- Restricted Boltzmann weight as a finite product of ordinary Wilson
Mayer factors. -/
theorem freeBoundaryBoltzmann_eq_prod
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G) :
    Real.exp (-β * freeBoundaryWilsonAction pe A) =
      ∏ p ∈ freeBoundaryPlaquettes (d := d) (N := N),
        (1 + plaquetteWeight pe β A p) := by
  unfold freeBoundaryWilsonAction plaquetteSubsetAction
  rw [show
    -β * (∑ p ∈ freeBoundaryPlaquettes (d := d) (N := N),
      pe (plaquetteHolonomy A p)) =
      ∑ p ∈ freeBoundaryPlaquettes (d := d) (N := N),
        (-β * pe (plaquetteHolonomy A p)) from
    Finset.mul_sum _ _ _]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  unfold plaquetteWeight
  ring

open Classical in
/-- The full product for the seam-deleted weight is exactly the product over
interior plaquettes. -/
theorem prod_one_add_freeBoundaryPlaquetteWeight
    (pe : G → ℝ) (β : ℝ) (A : GaugeConfig d N G) :
    (∏ p : ConcretePlaquette d N,
        (1 + freeBoundaryPlaquetteWeight pe β A p)) =
      ∏ p ∈ freeBoundaryPlaquettes (d := d) (N := N),
        (1 + plaquetteWeight pe β A p) := by
  unfold freeBoundaryPlaquetteWeight plaquetteSubsetWeight
  exact (prod_one_add_truncWeight
    (fun A p => plaquetteWeight pe β A p)
    (freeBoundaryPlaquettes (d := d) (N := N)) A).symm

/-- **Exact genuine-integral/polymer-gas bridge for free boundaries.** -/
theorem freeBoundaryPartitionFunction_eq_weightedPartition
    (μ : Measure G) (pe : G → ℝ) (β : ℝ) :
    freeBoundaryPartitionFunction (d := d) (N := N) μ pe β =
      weightedPartition (d := d) (N := N) μ
        (freeBoundaryPlaquetteWeight pe β) := by
  unfold freeBoundaryPartitionFunction weightedPartition
  congr 1
  funext A
  rw [freeBoundaryBoltzmann_eq_prod,
    prod_one_add_freeBoundaryPlaquetteWeight]

/-- The genuine free-boundary partition function is the periodic Wilson
polymer gas restricted to polymers contained in the non-wrapping region. -/
theorem freeBoundaryPartitionFunction_eq_partition_restrict
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    (freeBoundaryPartitionFunction
        (d := d) (N := N) μ pe β : ℂ) =
      KP.partition
        (weightedLatticePolymerSystem (d := d) (N := N) μ
          (fun A p => plaquetteWeight pe β A p))
        (Finset.univ.filter (fun c =>
          c.1 ⊆ freeBoundaryPlaquettes (d := d) (N := N))) := by
  let Q := freeBoundaryPlaquettes (d := d) (N := N)
  have hmeas : ∀ p : ConcretePlaquette d N,
      Measurable (fun A : GaugeConfig d N G =>
        plaquetteWeight pe β A p) := by
    intro p
    unfold plaquetteWeight
    exact (Real.measurable_exp.comp
      ((hpe_meas.comp (measurable_plaquetteHolonomy p)).const_mul
        (-β))).sub measurable_const
  have hbd : ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 :=
    fun A p => abs_plaquetteWeight_le pe β A p hpe
  calc
    (freeBoundaryPartitionFunction
        (d := d) (N := N) μ pe β : ℂ)
        = ((∫ A, ∏ p ∈ Q, (1 + plaquetteWeight pe β A p)
              ∂(gaugeMeasureFrom (d := d) (N := N) μ) : ℝ) : ℂ) := by
          apply congrArg
          unfold freeBoundaryPartitionFunction
          congr 1
          funext A
          exact freeBoundaryBoltzmann_eq_prod pe β A
    _ = KP.partition
          (weightedLatticePolymerSystem (d := d) (N := N) μ
            (fun A p => plaquetteWeight pe β A p))
          (Finset.univ.filter (fun c => c.1 ⊆ Q)) :=
      restricted_weightedPartition_eq_partition μ
        (isLocalWeight_plaquetteWeight pe β) hmeas hbd Q

/-- Under the periodic KP criterion the free-boundary partition function is
the exponential of the restricted cluster sum. -/
theorem freeBoundaryPartitionFunction_eq_exp_clusterSum_restrict
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    {a : (weightedLatticePolymerSystem (d := d) (N := N) μ
      (fun A p => plaquetteWeight pe β A p)).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (weightedLatticePolymerSystem (d := d) (N := N) μ
        (fun A p => plaquetteWeight pe β A p)) a) :
    (freeBoundaryPartitionFunction
        (d := d) (N := N) μ pe β : ℂ) =
      Complex.exp
        (KP.clusterSum
          ((weightedLatticePolymerSystem (d := d) (N := N) μ
            (fun A p => plaquetteWeight pe β A p)).restrict
            (Finset.univ.filter (fun c =>
              c.1 ⊆ freeBoundaryPlaquettes (d := d) (N := N))))) := by
  rw [freeBoundaryPartitionFunction_eq_partition_restrict
    μ hpe_meas hpe β]
  exact KP.partition_eq_exp_clusterSum_restrict hkp _

/-- Free-boundary expectation as the normalized genuine Boltzmann
numerator. -/
theorem freeBoundaryExpectation_eq_boltzmann_div
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : GaugeConfig d N G → ℝ) :
    freeBoundaryExpectation μ pe β O =
      (∫ A, O A * Real.exp (-β * freeBoundaryWilsonAction pe A)
        ∂(gaugeMeasureFrom (d := d) (N := N) μ)) /
      freeBoundaryPartitionFunction (d := d) (N := N) μ pe β := by
  unfold freeBoundaryExpectation freeBoundaryGibbsMeasure
    freeBoundaryPartitionFunction
  rw [integral_tilted, ← integral_div]
  congr 1
  funext A
  dsimp only
  rw [smul_eq_mul]
  ring

/-- Positivity of a finite-volume free-boundary expectation. -/
theorem freeBoundaryExpectation_nonneg
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : GaugeConfig d N G → ℝ)
    (hO : ∀ A, 0 ≤ O A) :
    0 ≤ freeBoundaryExpectation μ pe β O := by
  unfold freeBoundaryExpectation
  exact integral_nonneg hO

/-- The expectation of one is one under the genuine free-boundary Gibbs
probability measure. -/
theorem freeBoundaryExpectation_one
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) :
    freeBoundaryExpectation (d := d) (N := N) μ pe β (fun _ => 1) = 1 := by
  letI : IsProbabilityMeasure
      (freeBoundaryGibbsMeasure (d := d) (N := N) μ pe β) :=
    freeBoundaryGibbsMeasure_isProbability μ hpe_meas hpe β
  simp [freeBoundaryExpectation]

end FreeBoundary

namespace WindowPolymer

open FreeBoundary

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- Every complete marked set below a centered cutoff is itself retained by
the standard free box. -/
theorem markedSet_subset_freeBoundaryPlaquettes
    {n : ℕ}
    (O : CompatibleLocalObservable d G) (R K : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K) (hKR : K ≤ R) :
    S₀ ⊆
      FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1) := by
  intro q hq
  have hqMargin : q.SiteMargin 0 :=
    markedSet_siteMargin_residual
      O R K 0 hC hroom hpin hcard (by omega) hq
  exact FreeBoundary.mem_freeBoundaryPlaquettes_of_siteMargin_zero q hqMargin

/-- **A small support-rooted cluster cannot see the free boundary.**

The centered support starts with margin `2L`.  Cluster connectivity supplies
an actual plaquette-touching walk of length at most twice the total polymer
size.  Hence a cluster of total size `< L` has zero margin at every endpoint,
so every one of its plaquettes belongs to the standard free box.  This is the
geometric step which turns a boundary discrepancy into a literal size tail. -/
theorem smallCluster_subset_freeBoundaryPlaquettes
    (μ : Measure G)
    {n : ℕ}
    (w : GaugeConfig d (n + 1) G → ConcretePlaquette d (n + 1) → ℝ)
    (O : CompatibleLocalObservable d G) (L : ℕ)
    (hC : (O.center (2 * L + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (2 * L + 2) + 1 + (2 * L) + 1 < n + 1)
    {k : ℕ}
    {X : Fin k →
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ w) X)
    (hmeet : ∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes
        ((O.center (2 * L + 2)).realizedSupport n hC)))
    (hsmall : (∑ i, (X i).1.card) < L) :
    ∀ i, (X i).1 ⊆
      FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hmeet
  obtain ⟨p, hpX, hpS⟩ := Finset.not_disjoint_iff.mp hi₀
  have hpMargin : p.SiteMargin (2 * L) :=
    O.supportPlaquette_centered_siteMargin
      (2 * L) hC hroom hpS
  intro i q hq
  obtain ⟨W, hW⟩ :=
    weighted_exists_touchWalk_le μ w hX hpX hq
  have hWL : W.length ≤ 2 * L := by omega
  have hqMargin : q.SiteMargin 0 :=
    ConcretePlaquette.siteMargin_of_touchWalk W
      (hpMargin.mono (by simpa using hWL))
  exact FreeBoundary.mem_freeBoundaryPlaquettes_of_siteMargin_zero q hqMargin

/-- The corresponding statement for the combined support of the observable
and a complete marked set.  The residual-margin hypothesis is exactly the
one used by the marked Cauchy transport: the marked component consumes at
most `K` units, and the normalization cluster consumes fewer than `2L`. -/
theorem smallCluster_unionMarkedSupport_subset_freeBoundaryPlaquettes
    (μ : Measure G)
    {n : ℕ}
    (w : GaugeConfig d (n + 1) G → ConcretePlaquette d (n + 1) → ℝ)
    (O : CompatibleLocalObservable d G) (R K L : ℕ)
    (hC : (O.center (R + 2)).minVolume ≤ n)
    (hroom :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    {S₀ : Finset (ConcretePlaquette d (n + 1))}
    (hpin : localNear
      ((O.center (R + 2)).realizedSupport n hC) S₀ = S₀)
    (hcard : S₀.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R)
    {k : ℕ}
    {X : Fin k →
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ w).Polymer}
    (hX : KP.IsCluster
      (weightedLatticePolymerSystem (d := d) (N := n + 1) μ w) X)
    (hmeet : ∃ i, ¬ Disjoint (X i).1
      (supportPlaquettes
        (((O.center (R + 2)).realizedSupport n hC) ∪
          S₀.biUnion plaquetteSupport)))
    (hsmall : (∑ i, (X i).1.card) < L) :
    ∀ i, (X i).1 ⊆
      FreeBoundary.freeBoundaryPlaquettes (d := d) (N := n + 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hmeet
  obtain ⟨p, hpX, hpS⟩ := Finset.not_disjoint_iff.mp hi₀
  have hpMargin : p.SiteMargin (2 * L) :=
    unionMarkedSupport_siteMargin
      O R K L hC hroom hpin hcard hres hpS
  intro i q hq
  obtain ⟨W, hW⟩ :=
    weighted_exists_touchWalk_le μ w hX hpX hq
  have hWL : W.length ≤ 2 * L := by omega
  have hqMargin : q.SiteMargin 0 :=
    ConcretePlaquette.siteMargin_of_touchWalk W
      (hpMargin.mono (by simpa using hWL))
  exact FreeBoundary.mem_freeBoundaryPlaquettes_of_siteMargin_zero q hqMargin

/-- Free-boundary finite-volume value of a compatible local observable.
The side of the box is `n+1`, exactly as for `localGibbsExpectation`. -/
noncomputable def freeBoundaryLocalGibbsExpectation
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) : ℝ :=
  freeBoundaryExpectation (d := d) (N := n + 1)
    μ pe β (O.realize n)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Positivity survives at every finite free-boundary volume. -/
theorem freeBoundaryLocalGibbsExpectation_nonneg
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hO : ∀ A, 0 ≤ O.realize n A) :
    0 ≤ freeBoundaryLocalGibbsExpectation μ pe β O n := by
  exact freeBoundaryExpectation_nonneg μ pe β (O.realize n) hO

/-- The finite free-boundary expectation of the local unit is one. -/
theorem freeBoundaryLocalGibbsExpectation_one
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (n : ℕ) :
    freeBoundaryLocalGibbsExpectation μ pe β
      (CompatibleLocalObservable.const (d := d) (G := G) 1) n = 1 := by
  unfold freeBoundaryLocalGibbsExpectation
  simpa using
    freeBoundaryExpectation_one (d := d) (N := n + 1)
      μ hpe_meas hpe β

open Classical in
/-- The seam-deleted Mayer factor is local to the usual four positive edges
of its plaquette. -/
theorem dependsOnPos_freeBoundaryPlaquetteWeight_ofReal
    (pe : G → ℝ) (β : ℝ) (p : ConcretePlaquette d N) :
    DependsOnPos
      (fun A : GaugeConfig d N G =>
        (freeBoundaryPlaquetteWeight pe β A p : ℂ))
      (plaquetteSupport p) := by
  unfold freeBoundaryPlaquetteWeight FreeBoundary.plaquetteSubsetWeight
    truncWeight
  split_ifs with hp
  · exact dependsOnPos_plaquetteWeight_ofReal pe β p
  · intro x y hxy
    rfl

open Classical in
/-- Integrability of every finite seam-deleted Mayer monomial. -/
theorem integrable_prod_freeBoundaryPlaquetteWeight_ofReal
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (S : Finset (ConcretePlaquette d N)) :
    Integrable (fun A : GaugeConfig d N G =>
      ∏ p ∈ S, (freeBoundaryPlaquetteWeight pe β A p : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) μ) := by
  have hR := integrable_prod_weight
    (d := d) (N := N) μ
    (fun p =>
      FreeBoundary.measurable_plaquetteSubsetWeight
        (freeBoundaryPlaquettes (d := d) (N := N))
        hpe_meas β p)
    (fun A p =>
      FreeBoundary.abs_plaquetteSubsetWeight_le
        (freeBoundaryPlaquettes (d := d) (N := N))
        hpe β A p)
    S
  convert hR.ofReal (𝕜 := ℂ) using 1
  funext A
  push_cast
  rfl

open Classical in
/-- Integrability of a bounded compatible observable times every finite
seam-deleted Mayer monomial. -/
theorem integrable_realize_mul_prod_freeBoundaryPlaquetteWeight_ofReal
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (S : Finset (ConcretePlaquette d (n + 1))) :
    Integrable (fun A : GaugeConfig d (n + 1) G =>
      (O.realize n A : ℂ) *
        ∏ p ∈ S, (freeBoundaryPlaquetteWeight pe β A p : ℂ))
      (gaugeMeasureFrom (d := d) (N := n + 1) μ) := by
  have hprod :=
    integrable_prod_freeBoundaryPlaquetteWeight_ofReal
      (d := d) (N := n + 1) μ hpe_meas hpe β S
  have hOmeas : Measurable
      (fun A : GaugeConfig d (n + 1) G =>
        (O.realize n A : ℂ)) :=
    (O.measurable_realize n).complex_ofReal
  have hmul := hprod.bdd_mul hOmeas.aestronglyMeasurable
    (ae_of_all _ fun A => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        O.abs_realize_le n A)
  simpa [mul_comm] using hmul

/-- Unnormalized numerator of the genuine free-boundary local
expectation, written in Mayer-product form. -/
noncomputable def freeBoundaryLocalGibbsNumerator
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) : ℂ :=
  ∫ A, (O.realize n A : ℂ) *
      ∏ p : ConcretePlaquette d (n + 1),
        ((1 : ℂ) + (freeBoundaryPlaquetteWeight pe β A p : ℂ))
    ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)

open Classical in
/-- Exact marked expansion of the genuine free-boundary numerator. -/
theorem freeBoundaryLocalGibbsNumerator_eq_markedSum
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    freeBoundaryLocalGibbsNumerator μ pe β O n
      = ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
          (∫ A, (O.realize n A : ℂ) *
              ∏ p ∈ S₀,
                (freeBoundaryPlaquetteWeight pe β A p : ℂ)
              ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
          ∫ A, ∏ p ∈ localFarRegion (O.realizedSupport n hvol) S₀,
              ((1 : ℂ) +
                (freeBoundaryPlaquetteWeight pe β A p : ℂ))
            ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ) := by
  unfold freeBoundaryLocalGibbsNumerator
  exact integral_localSupport_tagged_expansion μ
    (fun A : GaugeConfig d (n + 1) G => (O.realize n A : ℂ))
    (O.realizedSupport n hvol) (O.dependsOnPos_realize n hvol)
    (fun p A => (freeBoundaryPlaquetteWeight pe β A p : ℂ))
    (dependsOnPos_freeBoundaryPlaquetteWeight_ofReal pe β)
    (fun S =>
      integrable_realize_mul_prod_freeBoundaryPlaquetteWeight_ofReal
        μ hpe_meas hpe β O n S)
    (fun S =>
      integrable_prod_freeBoundaryPlaquetteWeight_ofReal
        μ hpe_meas hpe β S)

open Classical in
/-- The genuine free-boundary local expectation is exactly its marked
numerator divided by the exact seam-deleted weighted partition function. -/
theorem freeBoundaryLocalGibbsExpectation_eq_numerator_div
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ) :
    (freeBoundaryLocalGibbsExpectation μ pe β O n : ℂ) =
      freeBoundaryLocalGibbsNumerator μ pe β O n /
        (weightedPartition (d := d) (N := n + 1) μ
          (freeBoundaryPlaquetteWeight pe β) : ℂ) := by
  unfold freeBoundaryLocalGibbsExpectation
  rw [freeBoundaryExpectation_eq_boltzmann_div, Complex.ofReal_div,
    freeBoundaryPartitionFunction_eq_weightedPartition]
  congr 1
  unfold freeBoundaryLocalGibbsNumerator
  rw [← integral_complex_ofReal]
  congr 1
  funext A
  push_cast
  congr 1
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (freeBoundaryBoltzmann_eq_prod
      (d := d) (N := n + 1) pe β A)
  have hprod := congrArg (fun r : ℝ => (r : ℂ))
    (prod_one_add_freeBoundaryPlaquetteWeight
      (d := d) (N := n + 1) pe β A)
  push_cast at h hprod
  exact h.trans hprod.symm

open Classical in
/-- **Exact one-volume free-boundary bridge.**  No convergence or boundary
comparison is assumed: this is the normalized marked expansion of the
genuine seam-deleted Gibbs integral. -/
theorem freeBoundaryLocalGibbsExpectation_eq_markedSum_div
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (hvol : O.minVolume ≤ n) :
    (freeBoundaryLocalGibbsExpectation μ pe β O n : ℂ)
      = (∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
          (∫ A, (O.realize n A : ℂ) *
              ∏ p ∈ S₀,
                (freeBoundaryPlaquetteWeight pe β A p : ℂ)
              ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
          ∫ A, ∏ p ∈ localFarRegion (O.realizedSupport n hvol) S₀,
              ((1 : ℂ) +
                (freeBoundaryPlaquetteWeight pe β A p : ℂ))
            ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        (weightedPartition (d := d) (N := n + 1) μ
          (freeBoundaryPlaquetteWeight pe β) : ℂ) := by
  rw [freeBoundaryLocalGibbsExpectation_eq_numerator_div,
    freeBoundaryLocalGibbsNumerator_eq_markedSum
      μ hpe_meas hpe β O n hvol]

end WindowPolymer

end YangMills
