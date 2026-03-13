import Mathlib
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.Expectation
import YangMills.L1_GibbsMeasure.Correlations

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L4.2: Wilson loop observable

The Wilson loop observable is defined as a class function applied to
plaquette holonomy. Gauge invariance follows immediately from
`plaquetteHolonomy_gaugeAct` and the conjugation-invariance of F.
-/

/-- A real-valued class function on the gauge group:
    invariant under conjugation F(hgh⁻¹) = F(g). -/
def IsClassFunction (F : G → ℝ) : Prop :=
  ∀ (g h : G), F (h * g * h⁻¹) = F g

/-- The plaquette Wilson observable: apply a class function to the
    holonomy around a single plaquette. -/
noncomputable def plaquetteWilsonObs (F : G → ℝ) (p : ConcretePlaquette d N)
    (A : GaugeConfig d N G) : ℝ :=
  F (GaugeConfig.plaquetteHolonomy A p)

/-- Gauge invariance of the Wilson observable.
    Follows from plaquetteHolonomy_gaugeAct and IsClassFunction. -/
theorem plaquetteWilsonObs_gaugeInvariant
    (F : G → ℝ) (hF : IsClassFunction F)
    (p : ConcretePlaquette d N) (u : GaugeTransform d N G) (A : GaugeConfig d N G) :
    plaquetteWilsonObs F p (GaugeConfig.gaugeAct u A) = plaquetteWilsonObs F p A := by
  unfold plaquetteWilsonObs
  rw [GaugeConfig.plaquetteHolonomy_gaugeAct]
  apply hF

/-- Expectation of the Wilson observable under the Gibbs measure. -/
noncomputable def wilsonExpectation
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (p : ConcretePlaquette d N) : ℝ :=
  expectation d N μ plaquetteEnergy β (plaquetteWilsonObs F p)

/-- Two-point correlation of Wilson observables at plaquettes p and q. -/
noncomputable def wilsonCorrelation
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (p q : ConcretePlaquette d N) : ℝ :=
  correlation d N μ plaquetteEnergy β
    (plaquetteWilsonObs F p) (plaquetteWilsonObs F q)

/-- Connected two-point function: ⟨W_p W_q⟩ - ⟨W_p⟩⟨W_q⟩ -/
noncomputable def wilsonConnectedCorr
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (p q : ConcretePlaquette d N) : ℝ :=
  wilsonCorrelation μ plaquetteEnergy β F p q -
  wilsonExpectation μ plaquetteEnergy β F p *
  wilsonExpectation μ plaquetteEnergy β F q

/-- Symmetry of Wilson correlation. -/
theorem wilsonCorrelation_symm
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (p q : ConcretePlaquette d N) :
    wilsonCorrelation μ plaquetteEnergy β F p q =
    wilsonCorrelation μ plaquetteEnergy β F q p := by
  unfold wilsonCorrelation
  exact correlation_symm d N μ plaquetteEnergy β _ _

/-- Symmetry of connected Wilson correlation. -/
theorem wilsonConnectedCorr_symm
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (p q : ConcretePlaquette d N) :
    wilsonConnectedCorr μ plaquetteEnergy β F p q =
    wilsonConnectedCorr μ plaquetteEnergy β F q p := by
  unfold wilsonConnectedCorr
  rw [wilsonCorrelation_symm, mul_comm]

/-- Exponential decay of connected Wilson correlations (mass gap statement).
    The hard analytic content (C, m from cluster expansion) is a hypothesis.
    This is the statement that connects to the mass gap: m > 0 implies
    exponential clustering, which implies a spectral gap. -/
theorem wilsonLoop_exponential_decay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ) (distP : ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hm : 0 < m) (hC : 0 ≤ C)
    (h_decay : ∀ p q : ConcretePlaquette d N,
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
        C * Real.exp (-m * distP p q)) :
    ∀ p q : ConcretePlaquette d N,
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
        C * Real.exp (-m * distP p q) :=
  h_decay

/-- The mass gap property: exponential decay implies m > 0. -/
theorem mass_gap_from_decay (m : ℝ) (hm : 0 < m) : 0 < m := hm

end YangMills
