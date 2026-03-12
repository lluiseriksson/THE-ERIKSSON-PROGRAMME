import Mathlib.MeasureTheory.Integral.Bochner
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

variable {α : Type _}

/-!
# L1.3a: Finite-volume expectation
Expectation of scalar observables under the finite-volume Gibbs measure.
-/

section RealExpectation

variable {d N : ℕ} {G : Type _}
variable [Group G]
variable (β : ℝ)

/-- Expectation of a real-valued observable under the Gibbs measure. -/
noncomputable def expectation (O : GaugeConfig d N G → ℝ) : ℝ :=
  ∫ U, O U ∂(gibbsMeasure (d := d) (N := N) (G := G) β)

/--
Expectation of a constant observable, assuming the Gibbs measure is normalized.
This theorem should only be enabled once `gibbsMeasure` is proved to be a probability measure.
-/
theorem expectation_const
    (hprob : IsProbabilityMeasure (gibbsMeasure (d := d) (N := N) (G := G) β))
    (c : ℝ) :
    expectation (d := d) (N := N) (G := G) β (fun _ => c) = c := by
  -- final proof depends on the exact probability-measure API available in your Gibbs module
  sorry

end RealExpectation

end YangMills
