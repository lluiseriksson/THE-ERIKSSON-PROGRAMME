/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedSmallCauchy
import YangMills.L1_GibbsMeasure.LocalObservableAlgebra
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

/-- The volume-independent high-temperature data used by every local
observable. -/
structure UniformLocalKPRegime (d : ℕ) [NeZero d] (B β : ℝ) where
  t : ℝ
  ε : ℝ
  η : ℝ
  t_nonneg : 0 ≤ t
  ε_pos : 0 < ε
  η_pos : 0 < η
  radius_tilt :
    ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1
  small_tilt :
    ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t
  radius_unitTilt :
    ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1
  small_unitTilt :
    ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t
  marked_radius :
    ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1

/-- Cauchy convergence supplied by a packaged uniform KP regime. -/
theorem UniformLocalKPRegime.cauchySeq
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    CauchySeq
      (fun n => (localGibbsExpectation μ pe β O n : ℂ)) :=
  cauchySeq_localGibbsExpectation_kpUniform
    μ hpe_meas hpe β κ.t κ.ε κ.η κ.t_nonneg κ.ε_pos κ.η_pos
      κ.radius_tilt κ.small_tilt κ.radius_unitTilt κ.small_unitTilt
      O κ.marked_radius

/-- The actual infinite-volume value of a local observable.  It is the limit
of the complete finite-volume sequence, selected from completeness of `ℂ`
after the explicit Cauchy theorem has been proved. -/
noncomputable def infiniteLocalGibbsExpectation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) : ℂ :=
  Classical.choose
    (cauchySeq_tendsto_of_complete
      (κ.cauchySeq μ hpe_meas hpe O))

/-- The full finite-volume sequence converges to the constructed value. -/
theorem tendsto_infiniteLocalGibbsExpectation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    Tendsto
      (fun n => (localGibbsExpectation μ pe β O n : ℂ))
      atTop
      (𝓝 (infiniteLocalGibbsExpectation μ hpe_meas hpe κ O)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete
      (κ.cauchySeq μ hpe_meas hpe O))

/-- Although the limit is constructed in `ℂ`, it is real because every
finite-volume Gibbs expectation is real. -/
theorem infiniteLocalGibbsExpectation_im
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    (infiniteLocalGibbsExpectation μ hpe_meas hpe κ O).im = 0 := by
  have him :=
    Complex.continuous_im.tendsto
      (infiniteLocalGibbsExpectation μ hpe_meas hpe κ O) |>.comp
      (tendsto_infiniteLocalGibbsExpectation μ hpe_meas hpe κ O)
  have hzero :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have himzero :
      Tendsto
        (fun n =>
          ((localGibbsExpectation μ pe β O n : ℂ)).im)
        atTop (𝓝 0) := by
    convert hzero using 1 <;> simp
  apply tendsto_nhds_unique him
  exact himzero

/-- Real-valued form of the infinite local Gibbs functional. -/
noncomputable def infiniteLocalGibbsStateValue
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) : ℝ :=
  (infiniteLocalGibbsExpectation μ hpe_meas hpe κ O).re

/-- The genuine real expectations converge to the real state value. -/
theorem tendsto_infiniteLocalGibbsStateValue
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    Tendsto
      (fun n => localGibbsExpectation μ pe β O n)
      atTop
      (𝓝 (infiniteLocalGibbsStateValue μ hpe_meas hpe κ O)) := by
  have h :=
    Complex.continuous_re.tendsto
      (infiniteLocalGibbsExpectation μ hpe_meas hpe κ O) |>.comp
      (tendsto_infiniteLocalGibbsExpectation μ hpe_meas hpe κ O)
  simpa [infiniteLocalGibbsStateValue] using h

/-- Every cofinal volume schedule converges to the same local state value.
This is the schedule-independence consequence of convergence of the complete
sequence, not a compactness or subsequence argument. -/
theorem tendsto_infiniteLocalGibbsStateValue_comp
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (volume : ℕ → ℕ) (hvolume : Tendsto volume atTop atTop) :
    Tendsto
      (fun k => localGibbsExpectation μ pe β O (volume k))
      atTop
      (𝓝 (infiniteLocalGibbsStateValue μ hpe_meas hpe κ O)) :=
  (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O).comp
    hvolume

/-- Normalization of the infinite-volume local Gibbs functional. -/
theorem infiniteLocalGibbsStateValue_one
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β) :
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.const (d := d) (G := G) 1) = 1 := by
  apply tendsto_nhds_unique
    (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.const (d := d) (G := G) 1))
  simpa [localGibbsExpectation_one μ hpe_meas hpe β] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- Positivity passes from pointwise nonnegative local kernels to the
infinite-volume functional. -/
theorem infiniteLocalGibbsStateValue_nonneg
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G)
    (hO : ∀ x, 0 ≤ O.kernel x) :
    0 ≤ infiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  apply ge_of_tendsto'
    (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O)
  intro n
  apply localGibbsExpectation_nonneg
  intro A
  unfold CompatibleLocalObservable.realize
  split_ifs
  · exact hO _
  · exact le_rfl

/-- Invariance of the infinite-volume functional under each positive unit
translation generator. -/
theorem infiniteLocalGibbsStateValue_translate
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) (i : Fin d) :
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ (O.translate i) =
      infiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  have hO :=
    tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O
  have hT :=
    tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ (O.translate i)
  have hEq :
      ∀ᶠ n in atTop,
        localGibbsExpectation μ pe β (O.translate i) n =
          localGibbsExpectation μ pe β O n := by
    filter_upwards
      [eventually_ge_atTop (O.translate i).minVolume] with n hn
    exact localGibbsExpectation_translate μ pe β O i n hn
  have hEq' :
      ∀ᶠ n in atTop,
        localGibbsExpectation μ pe β O n =
          localGibbsExpectation μ pe β (O.translate i) n :=
    hEq.mono fun _ hn => hn.symm
  exact tendsto_nhds_unique hT (hO.congr' hEq')

/-- Invariance under every finite word in the positive unit translation
generators.  This packages the generator statement without changing its
honest scope into a claim about a separately formalized `ℤ^d` action. -/
theorem infiniteLocalGibbsStateValue_translateList
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) (is : List (Fin d)) :
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (O.translateList is) =
      infiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  induction is generalizing O with
  | nil => rfl
  | cons i is ih =>
      exact (ih (O := O.translate i)).trans
        (infiniteLocalGibbsStateValue_translate
          μ hpe_meas hpe κ O i)

/-- Additivity of the infinite-volume functional on the exact coordinate
union of two local observables. -/
theorem infiniteLocalGibbsStateValue_add
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : CompatibleLocalObservable d G) :
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (CompatibleLocalObservable.add O P) =
      infiniteLocalGibbsStateValue μ hpe_meas hpe κ O +
        infiniteLocalGibbsStateValue μ hpe_meas hpe κ P := by
  have hAdd :=
    tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.add O P)
  have hSum :=
    (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O).add
      (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ P)
  have hEq :
      ∀ᶠ n in atTop,
        localGibbsExpectation μ pe β
            (CompatibleLocalObservable.add O P) n =
          localGibbsExpectation μ pe β O n +
            localGibbsExpectation μ pe β P n := by
    filter_upwards
      [eventually_ge_atTop (max O.minVolume P.minVolume)] with n hn
    exact localGibbsExpectation_add μ hpe_meas hpe β O P n hn
  have hEq' :
      ∀ᶠ n in atTop,
        localGibbsExpectation μ pe β O n +
            localGibbsExpectation μ pe β P n =
          localGibbsExpectation μ pe β
            (CompatibleLocalObservable.add O P) n := by
    filter_upwards [hEq] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hAdd (hSum.congr' hEq')

/-- Real scalar linearity of the infinite-volume functional. -/
theorem infiniteLocalGibbsStateValue_smul
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (c : ℝ) (O : CompatibleLocalObservable d G) :
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (CompatibleLocalObservable.smul c O) =
      c * infiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  have hScalar :=
    tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.smul c O)
  have hMul :=
    (tendsto_const_nhds.mul
      (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O) :
      Tendsto
        (fun n : ℕ => c * localGibbsExpectation μ pe β O n)
        atTop
        (𝓝 (c * infiniteLocalGibbsStateValue μ hpe_meas hpe κ O)))
  have hEq :
      ∀ᶠ n in atTop,
        localGibbsExpectation μ pe β
            (CompatibleLocalObservable.smul c O) n =
          c * localGibbsExpectation μ pe β O n := by
    filter_upwards [eventually_ge_atTop O.minVolume] with n hn
    exact localGibbsExpectation_smul μ pe β c O n hn
  have hEq' :
      ∀ᶠ n in atTop,
        c * localGibbsExpectation μ pe β O n =
          localGibbsExpectation μ pe β
            (CompatibleLocalObservable.smul c O) n := by
    filter_upwards [hEq] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hScalar (hMul.congr' hEq')

/-- Finite-volume truncated correlation of two compatible local
observables. -/
noncomputable def localGibbsTruncatedCorrelation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O P : CompatibleLocalObservable d G) (n : ℕ) : ℝ :=
  localGibbsExpectation μ pe β (CompatibleLocalObservable.mul O P) n -
    localGibbsExpectation μ pe β O n *
      localGibbsExpectation μ pe β P n

/-- Truncated correlation in the constructed infinite-volume state. -/
noncomputable def infiniteLocalGibbsTruncatedCorrelation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : CompatibleLocalObservable d G) : ℝ :=
  infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.mul O P) -
    infiniteLocalGibbsStateValue μ hpe_meas hpe κ O *
      infiniteLocalGibbsStateValue μ hpe_meas hpe κ P

/-- The complete finite-volume sequence of truncated correlations converges
to the truncated correlation of the infinite-volume state. -/
theorem tendsto_infiniteLocalGibbsTruncatedCorrelation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : CompatibleLocalObservable d G) :
    Tendsto
      (localGibbsTruncatedCorrelation μ pe β O P)
      atTop
      (𝓝 (infiniteLocalGibbsTruncatedCorrelation
        μ hpe_meas hpe κ O P)) := by
  exact
    (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (CompatibleLocalObservable.mul O P)).sub
      ((tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O).mul
        (tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ P))

/-- Any eventual volume-uniform bound on genuine finite Gibbs truncated
correlations passes unchanged to the infinite-volume state. -/
theorem abs_infiniteLocalGibbsTruncatedCorrelation_le_of_eventually
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : CompatibleLocalObservable d G) (C : ℝ)
    (hC : ∀ᶠ n in atTop,
      |localGibbsTruncatedCorrelation μ pe β O P n| ≤ C) :
    |infiniteLocalGibbsTruncatedCorrelation
      μ hpe_meas hpe κ O P| ≤ C := by
  exact le_of_tendsto
    ((tendsto_infiniteLocalGibbsTruncatedCorrelation
      μ hpe_meas hpe κ O P).abs) hC

/-- A positive normalized real state on the algebra of compatible local
observables, invariant under every positive unit translation generator and
every finite word in those generators.

This is an explicitly bundled positive normalized real linear functional on
the ordered local-observable space with unit.  It is not advertised as a
`C*`-algebraic state: no `C*` norm or completion is part of this file. -/
structure PositiveNormalizedLocalState
    (d : ℕ) [NeZero d]
    (G : Type*) [Group G] [MeasurableSpace G] where
  value : CompatibleLocalObservable d G → ℝ
  map_add : ∀ O P,
    value (CompatibleLocalObservable.add O P) = value O + value P
  map_smul : ∀ c O,
    value (CompatibleLocalObservable.smul c O) = c * value O
  map_one :
    value (CompatibleLocalObservable.const (d := d) (G := G) 1) = 1
  nonneg : ∀ O, (∀ x, 0 ≤ O.kernel x) → 0 ≤ value O
  translate : ∀ O i, value (O.translate i) = value O
  translateList : ∀ O is, value (O.translateList is) = value O

instance
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G] :
    CoeFun (PositiveNormalizedLocalState d G)
      (fun _ => CompatibleLocalObservable d G → ℝ) :=
  ⟨PositiveNormalizedLocalState.value⟩

/-- **The infinite-volume positive, normalized local Gibbs state, invariant
under all finite words in the positive translation generators.** -/
noncomputable def infiniteLocalGibbsState
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β) :
    PositiveNormalizedLocalState d G where
  value := infiniteLocalGibbsStateValue μ hpe_meas hpe κ
  map_add := infiniteLocalGibbsStateValue_add μ hpe_meas hpe κ
  map_smul := infiniteLocalGibbsStateValue_smul μ hpe_meas hpe κ
  map_one := infiniteLocalGibbsStateValue_one μ hpe_meas hpe κ
  nonneg := infiniteLocalGibbsStateValue_nonneg μ hpe_meas hpe κ
  translate := infiniteLocalGibbsStateValue_translate μ hpe_meas hpe κ
  translateList :=
    infiniteLocalGibbsStateValue_translateList μ hpe_meas hpe κ

end WindowPolymer

end YangMills
