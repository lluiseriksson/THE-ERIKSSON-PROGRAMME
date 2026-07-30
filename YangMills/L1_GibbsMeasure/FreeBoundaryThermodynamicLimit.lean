/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit
import YangMills.L1_GibbsMeasure.LocalBoundaryCorrection

/-!
# The thermodynamic limit with a genuine free boundary

This file compares a concrete cofinal exhaustion by centered free boxes with
the complete periodic finite-volume sequence.  The comparison tends to zero
by the same explicit marked KP tails used in the Cauchy proof.  Consequently
the whole free sequence, not merely a subsequence, converges to the already
constructed infinite-volume state.
-/

namespace YangMills

open MeasureTheory GaugeConfig Filter Topology

namespace WindowPolymer

open Classical

/-- A cofinal volume index at which the radius-`3q+1` centered window is
admissible. -/
noncomputable def freeBoundaryVolumeIndex
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (q : ℕ) : ℕ :=
  thermodynamicVolumeThreshold O q + q

/-- The chosen free-box volume indices tend to infinity. -/
theorem tendsto_freeBoundaryVolumeIndex
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) :
    Tendsto (freeBoundaryVolumeIndex O) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, ?_⟩
  intro a ha
  unfold freeBoundaryVolumeIndex
  omega

/-- The centered window is admissible at every chosen free-box volume. -/
theorem freeBoundaryVolumeIndex_admissible
    {d q : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) :
    MarkedWindowAdmissible O (thermodynamicWindowRadius q)
      (freeBoundaryVolumeIndex O q) := by
  apply markedWindowAdmissible_of_threshold_le
  unfold freeBoundaryVolumeIndex
  omega

/-- The genuine free-boundary Gibbs expectation along the explicit centered
cofinal exhaustion. -/
noncomputable def freeBoundaryThermodynamicExpectation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G) (q : ℕ) : ℂ :=
  FreeBoundary.freeBoundaryExpectation
    (d := d) (N := freeBoundaryVolumeIndex O q + 1)
    μ pe β
    ((O.center (thermodynamicWindowRadius q + 2)).realize
      (freeBoundaryVolumeIndex O q))

/-- Eventually, the periodic and genuine free expectations at the same
explicit volume differ by at most the thermodynamic Cauchy error. -/
theorem eventually_norm_periodic_sub_freeBoundaryThermodynamicExpectation_le
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    ∀ᶠ q : ℕ in atTop,
      ‖(localGibbsExpectation μ pe β O
          (freeBoundaryVolumeIndex O q) : ℂ) -
        freeBoundaryThermodynamicExpectation μ pe β O q‖
        ≤ thermodynamicCauchyBound
          O B β κ.t κ.ε κ.η q := by
  have hCorrection :
      ∀ᶠ q : ℕ in atTop,
        markedCorrectionCauchyBound O κ.t κ.ε q q ≤ 1 := by
    have hlt :
        ∀ᶠ q : ℕ in atTop,
          markedCorrectionCauchyBound O κ.t κ.ε q q < 1 :=
      (tendsto_order.1
        (tendsto_markedCorrectionCauchyBound_diagonal
          O κ.t κ.ε κ.ε_pos)).2 1 zero_lt_one
    exact hlt.mono fun _ hq => hq.le
  filter_upwards [hCorrection] with q hq
  have hres :
      (2 * q + 1) + q ≤ thermodynamicWindowRadius q := by
    simp [thermodynamicWindowRadius]
    omega
  simpa [freeBoundaryThermodynamicExpectation,
      thermodynamicCauchyBound] using
    (norm_localGibbsExpectation_sub_freeBoundary_le_kpUniform
      μ hpe_meas hpe β κ O
      (thermodynamicWindowRadius q) q q
      (freeBoundaryVolumeIndex_admissible O)
      hres hq)

/-- **Whole-sequence free-boundary thermodynamic limit.**

The explicit cofinal sequence of genuine free boxes converges to the same
infinite-volume value as periodic boundary conditions.  No compactness or
subsequence extraction occurs. -/
theorem tendsto_freeBoundaryThermodynamicExpectation
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    Tendsto
      (freeBoundaryThermodynamicExpectation μ pe β O)
      atTop
      (𝓝 (infiniteLocalGibbsExpectation
        μ hpe_meas hpe κ O)) := by
  let periodic : ℕ → ℂ := fun q =>
    (localGibbsExpectation μ pe β O
      (freeBoundaryVolumeIndex O q) : ℂ)
  let free : ℕ → ℂ :=
    freeBoundaryThermodynamicExpectation μ pe β O
  have hPeriodic :
      Tendsto periodic atTop
        (𝓝 (infiniteLocalGibbsExpectation
          μ hpe_meas hpe κ O)) := by
    exact (tendsto_infiniteLocalGibbsExpectation
      μ hpe_meas hpe κ O).comp
        (tendsto_freeBoundaryVolumeIndex O)
  have hNormError :
      Tendsto (fun q => ‖periodic q - free q‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · simpa [periodic, free] using
        (eventually_norm_periodic_sub_freeBoundaryThermodynamicExpectation_le
          μ hpe_meas hpe κ O)
    · exact tendsto_thermodynamicCauchyBound
        O B β κ.t κ.ε κ.η κ.ε_pos κ.η_pos
  have hError :
      Tendsto (fun q => periodic q - free q)
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNormError
  have hFree :
      Tendsto (fun q => periodic q - (periodic q - free q))
        atTop
        (𝓝 (infiniteLocalGibbsExpectation
          μ hpe_meas hpe κ O - 0)) :=
    hPeriodic.sub hError
  simpa [periodic, free] using hFree

end WindowPolymer

end YangMills
