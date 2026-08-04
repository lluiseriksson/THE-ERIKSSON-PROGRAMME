/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.ThermodynamicLimit
import YangMills.L1_GibbsMeasure.TwoPlaquetteCorrelator

/-!
# Passing the normalized two-plaquette bound to infinite volume

The finite endpoint in `TwoPlaquetteCorrelator` is stated directly as a
quotient of Boltzmann integrals.  Here it is identified with the truncated
correlation of compatible local observables and then passed through the
whole-sequence thermodynamic limit.
-/

namespace YangMills

open MeasureTheory GaugeConfig Filter Topology

namespace WindowPolymer

/-- The normalized two-plaquette estimate, expressed in the local-observable
language used by the thermodynamic limit. -/
theorem abs_localGibbsTruncatedCorrelation_le_twoPlaquette
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O P : CompatibleLocalObservable d G)
    {f : G → ℝ} (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t)
    (p q : ConcretePlaquette d (n + 1)) (k : ℕ) (hpq : p ≠ q)
    (hdist : 2 * k ≤ (touchGraph d (n + 1)).dist p q)
    (hone : 4 * Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1)
    (hvol : max O.minVolume P.minVolume ≤ n)
    (hO : ∀ A : GaugeConfig d (n + 1) G,
      O.realize n A = f (plaquetteHolonomy A p))
    (hP : ∀ A : GaugeConfig d (n + 1) G,
      P.realize n A = f (plaquetteHolonomy A q)) :
    |localGibbsTruncatedCorrelation μ pe β O P n|
      ≤ (8 * ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
          (1 + s) ^ 2 / s ^ 2) *
        Real.exp (-(ε * k)) := by
  have hMul :
      localGibbsExpectation μ pe β
          (CompatibleLocalObservable.mul O P) n =
        (∫ A, f (plaquetteHolonomy A p) *
            f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        partitionFunction (d := d) (N := n + 1) μ pe β := by
    rw [localGibbsExpectation_eq_boltzmann_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with A
    rw [CompatibleLocalObservable.realize_mul O P n hvol, hO A, hP A]
  have hOExp :
      localGibbsExpectation μ pe β O n =
        (∫ A, f (plaquetteHolonomy A p) *
            Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        partitionFunction (d := d) (N := n + 1) μ pe β := by
    rw [localGibbsExpectation_eq_boltzmann_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with A
    rw [hO A]
  have hPExp :
      localGibbsExpectation μ pe β P n =
        (∫ A, f (plaquetteHolonomy A q) *
            Real.exp (-β * wilsonAction pe A)
          ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) /
        partitionFunction (d := d) (N := n + 1) μ pe β := by
    rw [localGibbsExpectation_eq_boltzmann_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with A
    rw [hP A]
  unfold localGibbsTruncatedCorrelation
  rw [hMul, hOExp, hPExp]
  exact two_plaquette_correlator_bound_normalized
    μ hpe_meas hpe β hfm hf hs0 t ε ht0 hε0
      hr hsmall p q k hpq hdist hone

/-- The normalized exponential two-plaquette estimate passes unchanged to the
constructed infinite-volume state whenever the two local observables realize
the indicated separated plaquettes in every sufficiently large volume. -/
theorem abs_infiniteLocalGibbsTruncatedCorrelation_le_twoPlaquette
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : CompatibleLocalObservable d G)
    {f : G → ℝ} (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t)
    (k : ℕ)
    (hone : 4 * Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1)
    (hgeometry : ∀ᶠ n : ℕ in atTop,
      ∃ p q : ConcretePlaquette d (n + 1),
        p ≠ q ∧
        2 * k ≤ (touchGraph d (n + 1)).dist p q ∧
        max O.minVolume P.minVolume ≤ n ∧
        (∀ A : GaugeConfig d (n + 1) G,
          O.realize n A = f (plaquetteHolonomy A p)) ∧
        (∀ A : GaugeConfig d (n + 1) G,
          P.realize n A = f (plaquetteHolonomy A q))) :
    |infiniteLocalGibbsTruncatedCorrelation
        μ hpe_meas hpe κ O P|
      ≤ (8 * ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
          (1 + s) ^ 2 / s ^ 2) *
        Real.exp (-(ε * k)) := by
  apply abs_infiniteLocalGibbsTruncatedCorrelation_le_of_eventually
    μ hpe_meas hpe κ O P
  filter_upwards [hgeometry] with n hn
  obtain ⟨p, q, hpq, hdist, hvol, hO, hP⟩ := hn
  exact abs_localGibbsTruncatedCorrelation_le_twoPlaquette
    μ hpe_meas hpe β O P hfm hf hs0 t ε ht0 hε0
      hr hsmall p q k hpq hdist hone hvol hO hP

end WindowPolymer

end YangMills
