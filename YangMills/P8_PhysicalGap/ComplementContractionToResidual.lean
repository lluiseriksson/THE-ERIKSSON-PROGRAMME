import YangMills.P8_PhysicalGap.VacuumProjectorAlgebra

/-!
## C93: ComplementContractionToResidual

Removes the live  residual-contraction hypothesis
  ∀ x, P₀ x = 0 → ‖(T - P₀) x‖ ≤ exp(-m) * ‖x‖
by deriving it from the weaker assumption that T itself contracts on ker P₀.
-/

namespace YangMills

open ContinuousLinearMap MeasureTheory

section ComplementContraction

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- C93-H1: On ker P₀, the residual (T - P₀) acts exactly as T,
    provided T * P₀ = P₀. -/
theorem residual_eq_on_projector_kernel
    (T P₀ : H →L[ℝ] H)
    (hTP : T * P₀ = P₀)
    {x : H} (hx : P₀ x = 0) :
    (T - P₀) x = T x := by
  simp [ContinuousLinearMap.sub_apply, hx]

/-- C93-H2: If T contracts on ker P₀, then (T - P₀) also contracts on ker P₀. -/
theorem complementResidualContraction_of_complementContraction
    (T P₀ : H →L[ℝ] H)
    (m : ℝ)
    (hTP : T * P₀ = P₀)
    (hcompT : ∀ x : H, P₀ x = 0 → ‖T x‖ ≤ Real.exp (-m) * ‖x‖) :
    ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖ := by
  intro x hx
  rw [residual_eq_on_projector_kernel T P₀ hTP hx]
  exact hcompT x hx

end ComplementContraction

section FullChain

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- C93-T1: ClayYangMills from the weaker complement-contraction assumption.
    Wraps physicalStrong_of_profiledComplementResidualContraction_rankOneVacuum_biFixed
    by first deriving residual contraction via H2. -/
theorem physicalStrong_of_profiledComplementContraction_rankOneVacuum_biFixed
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω)
    (hfixAdj : T.adjoint Ω = Ω)
    (m : ℝ) (hm : 0 < m)
    (hcompT : ∀ x : H, P₀ x = 0 → ‖T x‖ ≤ Real.exp (-m) * ‖x‖)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  have hTP : T * P₀ = P₀ := by
    rw [hP₀eq]; exact rankOneProjector_absorb_left_of_fixed T Ω hfix
  have hcomp : ∀ x : H, P₀ x = 0 → ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖ :=
    complementResidualContraction_of_complementContraction T P₀ m hTP hcompT
  exact physicalStrong_of_profiledComplementResidualContraction_rankOneVacuum_biFixed
    Ω hΩ hP₀eq hfix hfixAdj m hm hcomp hopnorm hdistP

end FullChain

end YangMills
