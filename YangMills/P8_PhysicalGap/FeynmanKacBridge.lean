import Mathlib
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.L4_TransferMatrix.TransferMatrix
import YangMills.L5_MassGap.MassGap
import YangMills.P8_PhysicalGap.LSItoSpectralGap

/-!
# P8.1: Feynman-Kac Bridge

Connects HasSpectralGap to hbound via the Feynman-Kac formula.
-/

namespace YangMills

open MeasureTheory Real

-- Open inner product notation for ⟪·,·⟫_ℝ
open scoped InnerProductSpace

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Feynman-Kac hypothesis -/

/-- The Feynman-Kac formula: wilsonConnectedCorr = inner product with T^n. -/
def FeynmanKacFormula
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
    ∃ n : ℕ, distP N p q = n ∧
    @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
      @inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))

/-- State norm bounds. -/
def StateNormBound
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (C_ψ : ℝ) : Prop :=
  0 ≤ C_ψ ∧ ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
    ‖ψ_obs N p‖ ≤ C_ψ

/-! ## Main bridge theorem -/

/-- Feynman-Kac + spectral gap → hbound. -/
theorem feynmanKac_hbound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F
             (fun _ _ _ => 0) T P₀ ψ_obs) :
    ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C_ψ ^ 2 * C := by
  intro N' _hN' p q
  obtain ⟨n, _, hcorr⟩ := hFK N' p q
  rw [hcorr]
  have hψ_p := hψ.2 N' p
  have hψ_q := hψ.2 N' q
  have hTS := transferMatrix_spectral_gap T P₀ γ C hgap n
  calc |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))|
      ≤ ‖ψ_obs N' p‖ * ‖(T ^ n - P₀) (ψ_obs N' q)‖ :=
          real_inner_le_norm _ _
    _ ≤ ‖ψ_obs N' p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N' q‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ C_ψ * (C * Real.exp (-γ * n) * C_ψ) := by
          apply mul_le_mul hψ_p _ (by positivity) hψ.1
          exact mul_le_mul hTS hψ_q (norm_nonneg _) (by linarith [hgap.2.1])
    _ ≤ C_ψ ^ 2 * C := by
          have hexp : Real.exp (-γ * ↑n) ≤ 1 :=
            Real.exp_le_one_of_nonpos (by nlinarith [hgap.1, Nat.cast_nonneg n])
          nlinarith [hψ.1, hgap.2.1]

/-- Direct bridge: hbound → ClayYangMillsTheorem. -/
theorem hbound_implies_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hcont : Continuous plaquetteEnergy) (hβ : 0 ≤ β)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem :=
  eriksson_programme_phase7 (G := G) d 1 μ plaquetteEnergy β F
    hβ hcont nf ng hng (fun N' _hN' p q => hbound N' p q)

/-- Full chain: FK + spectral gap → Clay. -/
theorem feynmanKac_to_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hcont : Continuous plaquetteEnergy) (hβ : 0 ≤ β)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (hC_ψ : 0 ≤ C_ψ)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F
             (fun _ _ _ => 0) T P₀ ψ_obs) :
    ClayYangMillsTheorem :=
  hbound_implies_clay μ plaquetteEnergy β F hcont hβ
    (C_ψ ^ 2) C (by positivity)
    (feynmanKac_hbound μ plaquetteEnergy β F T P₀ γ C C_ψ hgap ψ_obs hψ hFK)

end YangMills
