/-
  C104: DistPNonnegFromFormula
  Derives hdistP (0 ≤ distP N p q) from FeynmanKacFormula alone.
  Key: FK says ∃ n : ℕ, distP N p q = ↑n, so 0 ≤ distP N p q by Nat.cast_nonneg.
  Also provides the 3-hypothesis minimal theorem:
  FeynmanKacFormula + StateNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong.
  Eliminates hdistP. Net: 4 → 3 live hyps. v1.20.0.
-/
import YangMills.P8_PhysicalGap.FeynmanKacToPhysicalStrong

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open MeasureTheory

/-- C104-H1: distP is non-negative whenever FeynmanKacFormula holds.
    Proof: FK gives ∃ n : ℕ, distP N p q = ↑n; since ↑n ≥ 0, we get 0 ≤ distP N p q. -/
theorem distPNonneg_of_feynmanKac
    {μ : Measure G}
    {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q := by
  intro N _ p q
  obtain ⟨n, hn_dist, _⟩ := hFK N p q
  rw [hn_dist]
  exact Nat.cast_nonneg n

/-- C104-T1 (v1.20.0): Minimal 3-hypothesis live-path theorem.
    FeynmanKacFormula + StateNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong.
    Proof: apply C103-T1, supplying hdistP via C104-H1 (distPNonneg_of_feynmanKac). -/
theorem physicalStrong_of_formula_stateNorm_hasSpectralGap_v2
    {μ : Measure G}
    {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {C_ψ γ C_gap : ℝ}
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C_gap) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_formula_stateNorm_hasSpectralGap hψ hFK hgap
    (distPNonneg_of_feynmanKac hFK)

end YangMills
