import YangMills.L1_GibbsMeasure.Expectation

namespace YangMills

/-!
# L1.3b: Generic finite-volume correlations
-/

section RealCorrelations

variable {d N : ℕ} {G : Type _}
variable [Group G]

/-- Correlation of two real-valued observables under the Gibbs measure. -/
noncomputable def correlation (β : ℝ)
    (O₁ O₂ : GaugeConfig d N G → ℝ) : ℝ :=
  expectation (d := d) (N := N) (G := G) β (fun U => O₁ U * O₂ U)

end RealCorrelations

end YangMills
