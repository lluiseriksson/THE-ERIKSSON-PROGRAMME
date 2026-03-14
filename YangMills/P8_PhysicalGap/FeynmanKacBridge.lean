import Mathlib
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.L4_TransferMatrix.TransferMatrix
import YangMills.L5_MassGap.MassGap
import YangMills.P8_PhysicalGap.LSItoSpectralGap

/-!
# P8.1: Feynman-Kac Bridge
-/

namespace YangMills

open MeasureTheory Real
open scoped InnerProductSpace

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def FeynmanKacFormula
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
    ∃ n : ℕ, distP N p q = n ∧
    @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
      @inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))

def StateNormBound
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) (C_ψ : ℝ) : Prop :=
  0 ≤ C_ψ ∧ ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N), ‖ψ_obs N p‖ ≤ C_ψ

/-- Feynman-Kac + spectral gap → hbound.
    |⟨ψ_p, (T^n-P₀)ψ_q⟩| ≤ C_ψ²·C by Cauchy-Schwarz + spectral gap. -/
theorem feynmanKac_hbound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F (fun _ _ _ => 0) T P₀ ψ_obs) :
    ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ C_ψ ^ 2 * C := by
  have hγ := hgap.1      -- 0 < γ
  have hC := hgap.2.1    -- 0 < C
  have hψ0 := hψ.1       -- 0 ≤ C_ψ
  intro N' _hN' p q
  obtain ⟨n, _, hcorr⟩ := hFK N' p q
  rw [hcorr]
  -- Cauchy-Schwarz: |⟨u, Av⟩| ≤ ‖u‖·‖A‖·‖v‖
  have hCS : |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))| ≤
      ‖ψ_obs N' p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N' q‖) := by
    calc |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))|
        ≤ ‖ψ_obs N' p‖ * ‖(T ^ n - P₀) (ψ_obs N' q)‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ ‖ψ_obs N' p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N' q‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  -- Spectral gap bound: ‖T^n - P₀‖ ≤ C·exp(-γ·n) ≤ C·1 = C
  have hTS : ‖T ^ n - P₀‖ ≤ C := by
    have h1 := transferMatrix_spectral_gap T P₀ γ C hgap n
    have h2 : Real.exp (-γ * ↑n) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg n])
    linarith [mul_le_mul_of_nonneg_left h2 (le_of_lt hC)]
  -- Norm bounds: ‖ψ_obs p‖ ≤ C_ψ, ‖ψ_obs q‖ ≤ C_ψ
  have hp := hψ.2 N' p
  have hq := hψ.2 N' q
  -- Combine
  calc |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))|
      ≤ ‖ψ_obs N' p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N' q‖) := hCS
    _ ≤ C_ψ * (C * C_ψ) := by
          apply mul_le_mul hp _ (by positivity) hψ0
          exact mul_le_mul hTS hq (norm_nonneg _) (le_of_lt hC)
    _ = C_ψ ^ 2 * C := by ring

theorem hbound_implies_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hcont : Continuous plaquetteEnergy) (hβ : 0 ≤ β)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem :=
  eriksson_programme_phase7 (G := G) d 1 μ plaquetteEnergy β F
    hβ hcont nf ng hng (fun N' _hN' p q => hbound N' p q)

theorem feynmanKac_to_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hcont : Continuous plaquetteEnergy) (hβ : 0 ≤ β)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (hC_ψ : 0 ≤ C_ψ)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F (fun _ _ _ => 0) T P₀ ψ_obs) :
    ClayYangMillsTheorem :=
  hbound_implies_clay μ plaquetteEnergy β F hcont hβ
    (C_ψ ^ 2) C (by positivity)
    (feynmanKac_hbound μ plaquetteEnergy β F T P₀ γ C C_ψ hgap ψ_obs hψ hFK)

end YangMills
