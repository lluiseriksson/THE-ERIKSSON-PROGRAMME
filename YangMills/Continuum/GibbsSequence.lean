/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.Continuum.Scale
import YangMills.Continuum.ObservableEmbedding

/-!
# Scale-indexed sequences of genuine thermodynamic Gibbs states

`GibbsStateSequence` stores finite-lattice input data and a uniform-KP regime
at every scale.  Its state is *defined* by
`integerInfiniteLocalGibbsState`; no arbitrary state functional is a field.
This is the main anti-vacuity gate of CONTINUUM-C0.
-/

namespace YangMills.Continuum

open Filter MeasureTheory Topology
open YangMills WindowPolymer

variable {A : Type*}
variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

/-- Scale-indexed data from which the repository constructs actual
thermodynamic Gibbs states.  In particular there is no `state` field. -/
structure GibbsStateSequence
    (d : ℕ) [NeZero d]
    (G : Type*) [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] where
  scale : ScaleSequence
  measure : Measure G
  measure_probability : IsProbabilityMeasure measure
  plaquetteEnergy : G → ℝ
  plaquetteEnergy_measurable : Measurable plaquetteEnergy
  energyBound : ℝ
  plaquetteEnergy_bounded :
    ∀ g, |plaquetteEnergy g| ≤ energyBound
  coupling : ℕ → ℝ
  regime :
    ∀ n, UniformLocalKPRegime d energyBound (coupling n)

namespace GibbsStateSequence

/-- The state at scale `n`, constructed by the existing thermodynamic-limit
theorem from the sequence's genuine Gibbs data. -/
noncomputable def state (S : GibbsStateSequence d G) (n : ℕ) :
    TranslationInvariantLocalState d G := by
  letI : IsProbabilityMeasure S.measure := S.measure_probability
  exact integerInfiniteLocalGibbsState
    S.measure S.plaquetteEnergy_measurable
    S.plaquetteEnergy_bounded (S.regime n)

/-- Evaluation of an embedded test by the constructed discrete state. -/
noncomputable def expectation
    (S : GibbsStateSequence d G)
    (E : ObservableEmbedding A d G)
    (n : ℕ) (F : A) : ℝ :=
  S.state n (E.atScale n F)

/-- A constant-coupling family remains scale-indexed through its genuine
spacing sequence.  This constructor is used only for the compiled mechanics
example; it does not assert that unrescaled constant-coupling observables have
the physical continuum scaling. -/
def constantCoupling
    (scale : ScaleSequence)
    (μ : Measure G) (hμ : IsProbabilityMeasure μ)
    (pe : G → ℝ) (hpe_meas : Measurable pe)
    (B β : ℝ) (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β) :
    GibbsStateSequence d G where
  scale := scale
  measure := μ
  measure_probability := hμ
  plaquetteEnergy := pe
  plaquetteEnergy_measurable := hpe_meas
  energyBound := B
  plaquetteEnergy_bounded := hpe
  coupling := fun _ => β
  regime := fun _ => κ

theorem constantCoupling_expectation
    (scale : ScaleSequence)
    (μ : Measure G) (hμ : IsProbabilityMeasure μ)
    (pe : G → ℝ) (hpe_meas : Measurable pe)
    (B β : ℝ) (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (E : ObservableEmbedding A d G) (n : ℕ) (F : A) :
    (constantCoupling scale μ hμ pe hpe_meas B β hpe κ).expectation E n F =
      (by
        letI : IsProbabilityMeasure μ := hμ
        exact integerInfiniteLocalGibbsState μ hpe_meas hpe κ
          (E.atScale n F)) := by
  rfl

end GibbsStateSequence

end YangMills.Continuum
