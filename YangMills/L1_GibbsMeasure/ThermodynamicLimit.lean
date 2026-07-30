/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedSmallCauchy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Thermodynamic limit of local Gibbs expectations

This file turns the direct two-volume marked-expansion estimate into a
whole-sequence Cauchy theorem and defines the resulting infinite-volume local
state.
-/

namespace YangMills

open MeasureTheory GaugeConfig Filter Topology

namespace WindowPolymer

open Classical

/-- The single-cutoff error used for the whole-sequence Cauchy argument:
`K = L = q`, while the common geometric window will be `R = 3q+1`. -/
noncomputable def thermodynamicCauchyBound
    {d : ℕ} {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (B β t ε η : ℝ) (q : ℕ) : ℝ :=
  2 * markedOuterTailBound O B β t η q +
    markedSmallLayerCauchyBound O B β t ε η q q

/-- Exponential decay beats an affine factor along the natural numbers. -/
theorem tendsto_exp_neg_mul_nat_mul_affine
    (ε a b : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun q : ℕ =>
        Real.exp (-(ε * (q : ℝ))) * (a + b * (q : ℝ)))
      atTop (𝓝 0) := by
  have hExp :
      Tendsto (fun q : ℕ => Real.exp (-(ε * (q : ℝ))))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  have hLin₀ :
      Tendsto
        (fun q : ℕ =>
          ((q : ℝ) ^ (1 : ℝ)) *
            Real.exp (-ε * (q : ℝ)))
        atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 ε hε).comp
      tendsto_natCast_atTop_atTop
  have hLin :
      Tendsto
        (fun q : ℕ =>
          (q : ℝ) * Real.exp (-(ε * (q : ℝ))))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul] using hLin₀
  convert (hExp.const_mul a).add (hLin.const_mul b) using 1
  · funext q
    ring
  · ring

/-- The explicit single-cutoff thermodynamic error tends to zero. -/
theorem tendsto_thermodynamicCauchyBound
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (B β t ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    Tendsto (thermodynamicCauchyBound O B β t ε η)
      atTop (𝓝 0) := by
  let A : ℝ :=
    O.bound *
      Real.exp (
        (2 * t) *
          ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))))
  let E : ℝ :=
    Real.exp (
      ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
        ((localMarkedEffectiveWeight d B β t * Real.exp η) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (localMarkedEffectiveWeight d B β t *
              Real.exp η))))
  have hOuter :
      Tendsto
        (fun q : ℕ =>
          2 * (A * (Real.exp (-(η * (q : ℝ))) * E)))
        atTop (𝓝 0) := by
    have h :=
      tendsto_exp_neg_mul_nat_mul_affine η E 0 hη
    simpa [mul_zero, add_zero, mul_assoc] using
      ((h.const_mul A).const_mul 2)
  have hSmall :
      Tendsto
        (fun q : ℕ =>
          (A *
            (2 *
              (2 * (Real.exp (-(ε * (q : ℝ))) *
                ((2 * t) *
                  (((Fintype.card O.Support + 4 * q : ℕ) : ℝ) *
                    (4 * (d : ℝ))))))) * E))
        atTop (𝓝 0) := by
    have h :=
      tendsto_exp_neg_mul_nat_mul_affine ε
        (((2 * t) *
          ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ)))))
        (((2 * t) * (4 * (4 * (d : ℝ))))) hε
    have h' := (((h.const_mul 2).const_mul 2).const_mul A).mul_const E
    convert h' using 1
    · funext q
      push_cast
      ring
    · ring
  have hAdd :
      Tendsto
        (fun q : ℕ =>
          2 * (A * (Real.exp (-(η * (q : ℝ))) * E)) +
          (A *
            (2 *
              (2 * (Real.exp (-(ε * (q : ℝ))) *
                ((2 * t) *
                  (((Fintype.card O.Support + 4 * q : ℕ) : ℝ) *
                    (4 * (d : ℝ))))))) * E))
        atTop (𝓝 0) := by
    simpa only [zero_add] using hOuter.add hSmall
  refine hAdd.congr' ?_
  filter_upwards with q
  simp only [thermodynamicCauchyBound, markedOuterTailBound,
    markedSmallLayerCauchyBound, markedCorrectionCauchyBound, A, E]

/-- The diagonal correction error required by the finite marked-layer
estimate also tends to zero. -/
theorem tendsto_markedCorrectionCauchyBound_diagonal
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (t ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun q => markedCorrectionCauchyBound O t ε q q)
      atTop (𝓝 0) := by
  have h :=
    tendsto_exp_neg_mul_nat_mul_affine ε
      (((2 * t) *
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ)))))
      (((2 * t) * (4 * (4 * (d : ℝ))))) hε
  have h' := h.const_mul 2
  convert h' using 1
  · funext q
    simp only [markedCorrectionCauchyBound]
    push_cast
    ring
  · ring

/-- The common-window radius attached to a single cutoff. -/
def thermodynamicWindowRadius (q : ℕ) : ℕ := 3 * q + 1

/-- A concrete volume threshold after which the centered observable and its
entire radius-`thermodynamicWindowRadius q` window fit without wrapping. -/
noncomputable def thermodynamicVolumeThreshold
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (q : ℕ) : ℕ :=
  max
    ((O.center (thermodynamicWindowRadius q + 2)).minVolume)
    (O.minVolume + (thermodynamicWindowRadius q + 2) + 1 +
      thermodynamicWindowRadius q + 1)

/-- Every volume above the explicit threshold is admissible for the common
window. -/
theorem markedWindowAdmissible_of_threshold_le
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (q : ℕ)
    (hn : thermodynamicVolumeThreshold O q ≤ n) :
    MarkedWindowAdmissible O (thermodynamicWindowRadius q) n := by
  constructor
  · exact (le_max_left _ _).trans hn
  · exact Nat.lt_succ_iff.mpr ((le_max_right _ _).trans hn)

/-- **Whole-sequence Cauchy theorem for every local Gibbs observable.**
The proof chooses a single cutoff from the explicit error bound, then an
explicit volume threshold.  It does not use compactness or extract a
subsequence. -/
theorem cauchySeq_localGibbsExpectation_kpUniform
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ)
    (ht0 : 0 ≤ t) (hε : 0 < ε) (hη : 0 < η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    CauchySeq
      (fun n => (localGibbsExpectation μ pe β O n : ℂ)) := by
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  have hBoundEv :
      ∀ᶠ q in atTop,
        thermodynamicCauchyBound O B β t ε η q < δ :=
    (tendsto_order.1
      (tendsto_thermodynamicCauchyBound O B β t ε η hε hη)).2
        δ hδ
  have hCorrectionEv :
      ∀ᶠ q in atTop,
        markedCorrectionCauchyBound O t ε q q ≤ 1 := by
    have hlt :
        ∀ᶠ q in atTop,
          markedCorrectionCauchyBound O t ε q q < 1 :=
      (tendsto_order.1
        (tendsto_markedCorrectionCauchyBound_diagonal O t ε hε)).2
          1 zero_lt_one
    exact hlt.mono fun _ hq => hq.le
  obtain ⟨q, hqBound, hqCorrection⟩ :=
    (hBoundEv.and hCorrectionEv).exists
  refine ⟨thermodynamicVolumeThreshold O q, ?_⟩
  intro n hn m hm
  have hnAdm :=
    markedWindowAdmissible_of_threshold_le O q hn
  have hmAdm :=
    markedWindowAdmissible_of_threshold_le O q hm
  have hpair :=
    norm_localGibbsExpectation_sub_le_kpUniform
      μ hpe_meas hpe β t ε η ht0 hε.le hη.le
        hr₀ hsmall₀ hr₁ hsmall₁ O
        (thermodynamicWindowRadius q) q q
        (by simp [thermodynamicWindowRadius]; omega)
        hnAdm hmAdm
        (by simp [thermodynamicWindowRadius]; omega)
        hqCorrection hrMarked
  rw [dist_eq_norm]
  exact hpair.trans_lt hqBound

end WindowPolymer

end YangMills
