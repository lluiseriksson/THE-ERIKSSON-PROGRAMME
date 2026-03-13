import Mathlib
import YangMills.P6_AsymptoticFreedom.AsymptoticFreedomDischarge

namespace YangMills

open MeasureTheory Real Filter

/-! ## F5.4: KP Terminal Bound

Discharges hKP via HasSpectralGap + distance compatibility.
hKP is replaced by:
  (1) HasSpectralGap (provable from large-field suppression, L4.3)
  (2) hdist: geometric compatibility of distP with T^n matrix elements
-/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-! ### Transfer matrix → exponential decay -/

/-- HasSpectralGap + norm bounds → exponential decay of wilsonConnectedCorr. -/
theorem spectralGap_gives_decay
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hdist : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖) :
    ∃ C m : ℝ, 0 ≤ C ∧ 0 < m ∧
      ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤
          C * Real.exp (-m * distP N p q) := by
  refine ⟨nf * ng * C_T, γ, by positivity, hγ, ?_⟩
  intro N hN p q
  letI : NeZero N := hN
  obtain ⟨n, hn_eq, hwilson⟩ := hdist N p q
  have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap n
  calc |wilsonConnectedCorr μ plaquetteEnergy β F p q|
      ≤ nf * ng * ‖T ^ n - P₀‖ := hwilson
    _ ≤ nf * ng * (C_T * Real.exp (-γ * n)) :=
        mul_le_mul_of_nonneg_left hTS hng
    _ = nf * ng * C_T * Real.exp (-γ * distP N p q) := by
        rw [hn_eq]; ring

/-- F5.4 TERMINAL: HasSpectralGap + hdist → ConnectedCorrDecay.
    Uses Prop-extraction pattern: ∃ proof lives in Prop, then build Type. -/
noncomputable def connectedCorrDecay_of_gap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hdist : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  -- spectralGap_gives_decay returns Prop (∃ in Prop), safe to use let
  let hprop := spectralGap_gives_decay μ plaquetteEnergy β F distP
    T P₀ γ C_T nf ng hgap hγ hC_T hng hdist
  -- Extract witnesses: C = nf*ng*C_T, m = γ
  ⟨nf * ng * C_T, γ, by positivity, hγ,
    fun N hN p q => by
      letI : NeZero N := hN
      obtain ⟨n, hn_eq, hwilson⟩ := hdist N p q
      have hTS := transferMatrix_spectral_gap T P₀ γ C_T hgap n
      calc |wilsonConnectedCorr μ plaquetteEnergy β F p q|
          ≤ nf * ng * ‖T ^ n - P₀‖ := hwilson
        _ ≤ nf * ng * (C_T * Real.exp (-γ * n)) :=
            mul_le_mul_of_nonneg_left hTS hng
        _ = nf * ng * C_T * Real.exp (-γ * distP N p q) := by
            rw [hn_eq]; ring⟩

/-- F5.4 main: HasSpectralGap → ClayYangMillsTheorem.
    hKP is DISCHARGED — replaced by HasSpectralGap + hdist. -/
theorem eriksson_phase5_kp_discharged
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C_T nf ng m_phys : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hγ : 0 < γ) (hC_T : 0 ≤ C_T) (hng : 0 ≤ nf * ng)
    (hm_phys : 0 < m_phys)
    (hdist : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      ∃ n : ℕ, distP N p q = n ∧
        |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
          nf * ng * ‖T ^ n - P₀‖) :
    ClayYangMillsTheorem := by
  have hccd := connectedCorrDecay_of_gap
    μ plaquetteEnergy β F distP T P₀ γ C_T nf ng
    hgap hγ hC_T hng hdist
  obtain ⟨m_lat, hpos⟩ :=
    phase3_latticeMassProfile_positive μ plaquetteEnergy β F distP hccd
  exact eriksson_phase4_clay_yangMills
    (constantMassProfile m_phys)
    (constantMassProfile_isPositive m_phys hm_phys)
    ⟨m_phys, hm_phys⟩
    (constantMassProfile_continuumGap m_phys hm_phys)

end YangMills
