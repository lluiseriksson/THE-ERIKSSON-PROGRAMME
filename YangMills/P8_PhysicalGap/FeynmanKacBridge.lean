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
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (C_ψ : ℝ) : Prop :=
  0 ≤ C_ψ ∧ ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
    ‖ψ_obs N p‖ ≤ C_ψ

theorem feynmanKac_hbound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F (fun _ _ _ => 0) T P₀ ψ_obs) :
    ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ C_ψ ^ 2 * C := by
  intro N' _hN' p q
  obtain ⟨n, _, hcorr⟩ := hFK N' p q
  rw [hcorr]
  have hψ_p := hψ.2 N' p
  have hψ_q := hψ.2 N' q
  have hTS := transferMatrix_spectral_gap T P₀ γ C hgap n
  have hC_pos := hgap.2.1
  have hγ_pos := hgap.1
  -- |⟨ψ_p, A ψ_q⟩| ≤ ‖ψ_p‖ · ‖A‖ · ‖ψ_q‖ ≤ C_ψ · (C·exp(-γn)) · C_ψ ≤ C_ψ²·C
  have step1 : |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))| ≤
      ‖ψ_obs N' p‖ * ‖(T ^ n - P₀) (ψ_obs N' q)‖ :=
    abs_real_inner_le_norm _ _
  have step2 : ‖(T ^ n - P₀) (ψ_obs N' q)‖ ≤ ‖T ^ n - P₀‖ * ‖ψ_obs N' q‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have step3 : ‖T ^ n - P₀‖ * ‖ψ_obs N' q‖ ≤ C * Real.exp (-γ * ↑n) * C_ψ :=
    mul_le_mul hTS hψ_q (norm_nonneg _) (by linarith)
  have step4 : C * Real.exp (-γ * ↑n) * C_ψ ≤ C * 1 * C_ψ := by
    apply mul_le_mul_of_nonneg_right _ hψ.1
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg n])
  calc |@inner ℝ H _ (ψ_obs N' p) ((T ^ n - P₀) (ψ_obs N' q))|
      ≤ ‖ψ_obs N' p‖ * ‖(T ^ n - P₀) (ψ_obs N' q)‖ := step1
    _ ≤ ‖ψ_obs N' p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N' q‖) :=
          mul_le_mul_of_nonneg_left step2 (norm_nonneg _)
    _ ≤ ‖ψ_obs N' p‖ * (C * Real.exp (-γ * ↑n) * C_ψ) :=
          mul_le_mul_of_nonneg_left step3 (norm_nonneg _)
    _ ≤ ‖ψ_obs N' p‖ * (C * 1 * C_ψ) :=
          mul_le_mul_of_nonneg_left step4 (norm_nonneg _)
    _ ≤ C_ψ * (C * C_ψ) := by
          simp only [mul_one]
          exact mul_le_mul_of_nonneg_right hψ_p (by nlinarith)
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
