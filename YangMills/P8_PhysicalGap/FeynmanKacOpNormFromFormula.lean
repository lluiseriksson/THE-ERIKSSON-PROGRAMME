/-
  C102: FeynmanKacOpNormFromFormula
  Derives FeynmanKacOpNormBound from FeynmanKacFormula + StateNormBound
  via a direct Cauchy-Schwarz chain. This eliminates FeynmanKacOpNormBound
  as a live hypothesis: callers need only supply FeynmanKacFormula (the
  exact transfer-matrix representation) and StateNormBound (norm control
  on the observation states).

  Key theorems:
  1. feynmanKacOpNormBound_of_formula_stateNorm (C102-H1):
       FeynmanKacFormula + StateNormBound -> FeynmanKacOpNormBound(C_psi^2)
     Proof: wCC = <psi_p,(T^n-P0)psi_q>  ->  |.|  ->  CS  ->  op-norm  ->  C_psi^2*||T^n-P0||
  2. physicalStrong_of_formula_stateNorm_rankOneVacuum_selfAdjoint (C102-T1):
       FeynmanKacFormula + StateNormBound + self-adjoint ket-invariant vacuum -> ClayYangMillsPhysicalStrong
     Proof: C102-H1 then C101 (physicalStrong_of_projectedOpNormBound_rankOneVacuum_selfAdjoint)

  Oracle expected: [propext, Classical.choice, Quot.sound] -- zero sorry.
-/
import Mathlib
import YangMills.P8_PhysicalGap.FeynmanKacBridge
import YangMills.P8_PhysicalGap.VacuumAdjointFixed

namespace YangMills

open ContinuousLinearMap MeasureTheory Real
open scoped InnerProductSpace

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **C102-H1**: FeynmanKacOpNormBound from FeynmanKacFormula + StateNormBound.

  The key step: wCC = ⟨ψ_p,(T^n-P₀)ψ_q⟩ (exact equality from FeynmanKacFormula)
  is converted to the Cauchy-Schwarz chain:
    |wCC| = |⟨ψ_p,(T^n-P₀)ψ_q⟩|
          ≤ ‖ψ_p‖ · ‖(T^n-P₀)ψ_q‖           (Cauchy-Schwarz)
          ≤ ‖ψ_p‖ · (‖T^n-P₀‖ · ‖ψ_q‖)       (op-norm)
          ≤ C_ψ · (‖T^n-P₀‖ · C_ψ)           (StateNormBound)
          = C_ψ² · ‖T^n-P₀‖                   (ring)

  This eliminates FeynmanKacOpNormBound as a live hypothesis: the constant
  C_fk = C_ψ² is determined by the state-norm bound. -/
theorem feynmanKacOpNormBound_of_formula_stateNorm
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {C_ψ : ℝ}
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ (C_ψ ^ 2) := by
  constructor
  · exact sq_nonneg C_ψ
  · intro N _ p q
    obtain ⟨n, hn_dist, hn_eq⟩ := hFK N p q
    -- hn_dist : distP N p q = ↑n
    -- hn_eq   : @wilsonConnectedCorr ... = @inner ℝ H _ (ψ_obs N p) ((T^n-P₀)(ψ_obs N q))
    refine ⟨n, hn_dist, ?_⟩
    -- goal: |@wilsonConnectedCorr ...| ≤ C_ψ^2 * ‖T^n - P₀‖
    rw [hn_eq]
    -- goal: |@inner ℝ H _ (ψ_obs N p) ((T^n-P₀)(ψ_obs N q))| ≤ C_ψ^2 * ‖T^n - P₀‖
    have hC_ψ : (0 : ℝ) ≤ C_ψ := hψ.1
    have hp   : ‖ψ_obs N p‖ ≤ C_ψ := hψ.2 N p
    have hq   : ‖ψ_obs N q‖ ≤ C_ψ := hψ.2 N q
    have hCS : |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))| ≤
        ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ :=
      abs_real_inner_le_norm _ _
    have hopnorm_ineq : ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤ ‖T ^ n - P₀‖ * ‖ψ_obs N q‖ :=
      ContinuousLinearMap.le_opNorm _ _
    calc |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))|
        ≤ ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ := hCS
      _ ≤ ‖ψ_obs N p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N q‖) :=
            mul_le_mul_of_nonneg_left hopnorm_ineq (norm_nonneg _)
      _ ≤ C_ψ * (‖T ^ n - P₀‖ * C_ψ) :=
            mul_le_mul hp (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
              (by positivity) hC_ψ
      _ = C_ψ ^ 2 * ‖T ^ n - P₀‖ := by ring

/-- **C102-T1**: ClayYangMillsPhysicalStrong from FeynmanKacFormula + StateNormBound +
  self-adjoint ket-invariant vacuum.

  Live-path chain:
    FeynmanKacFormula + StateNormBound
      ↓ C102-H1 (Cauchy-Schwarz)
    FeynmanKacOpNormBound(C_ψ²)
      ↓ C101 (self-adjoint + ket-invariance ⇒ T.adjoint Ω = Ω)
    ClayYangMillsPhysicalStrong

  After C102, the live bottleneck no longer includes FeynmanKacOpNormBound as a
  separate hypothesis: it is fully derived from FeynmanKacFormula + StateNormBound.
  The remaining open hypotheses on the path to ClayYangMillsPhysicalStrong are:
    (a) FeynmanKacFormula (exact FK representation of wCC as transfer-matrix inner product)
    (b) StateNormBound (norm bound on observation states ψ_obs)
    (c) hfix : T Ω = Ω (vacuum ket-invariance of transfer matrix)
    (d) hselfAdj : T.adjoint = T (self-adjointness of T)
    (e) hproj : ‖T * (1 - P₀)‖ ≤ exp(-m) (projected op-norm bound / spectral gap) -/
theorem physicalStrong_of_formula_stateNorm_rankOneVacuum_selfAdjoint
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) (C_ψ : ℝ)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hP₀eq : P₀ = (innerSL ℝ Ω).smulRight Ω)
    (hfix : T Ω = Ω) (hselfAdj : T.adjoint = T)
    (m : ℝ) (hm : 0 < m)
    (hproj : ‖T * ((1 : H →L[ℝ] H) - P₀)‖ ≤ Real.exp (-m))
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  -- Step 1: lift FK formula to operator-norm bound (C_fk = C_ψ^2)
  have hFKop : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ (C_ψ ^ 2) :=
    feynmanKacOpNormBound_of_formula_stateNorm hψ hFK
  -- Step 2: apply C101 (self-adjoint ket-invariance -> ClayYangMillsPhysicalStrong)
  exact physicalStrong_of_projectedOpNormBound_rankOneVacuum_selfAdjoint
    Ω hΩ hP₀eq hfix hselfAdj m hm hproj hFKop hdistP

end YangMills
