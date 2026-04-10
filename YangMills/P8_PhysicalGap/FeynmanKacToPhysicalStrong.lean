/-
  C103: FeynmanKacToPhysicalStrong
  Chains C102-H1 (FeynmanKacFormula + StateNormBound → FeynmanKacOpNormBound)
  with C87-2  (FeynmanKacOpNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong).
  Eliminates ALL vacuum-structure hypotheses. Net: 9+ → 4 live hyps. v1.19.0.
-/
import YangMills.P8_PhysicalGap.FeynmanKacOpNormFromFormula
import YangMills.P8_PhysicalGap.OperatorNormBound

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open MeasureTheory

/-- **C103-T1** (v1.19.0): Minimal live-path theorem.
    FeynmanKacFormula + StateNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong.
    Proof: C102-H1 then C87-2. One term; no vacuum structure needed. -/
theorem physicalStrong_of_formula_stateNorm_hasSpectralGap
    {μ : Measure G}
    {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {C_ψ γ C_gap : ℝ}
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C_gap)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  opNormBound_to_physicalStrong
    (feynmanKacOpNormBound_of_formula_stateNorm hψ hFK)
    hgap hdistP

end YangMills
