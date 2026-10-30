import YangMills.RG.RegularSectorCurve
import YangMills.RG.NonlinearTangentCoercivity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Local noncoercivity on an actual regular nonlinear sector. The actual IFT
curve is derived in RegularSectorCurve. Its energy is transported by exact
quadratic homogeneity and the derivative-as-slope limit, never by applying a
band estimate to a curve outside that band. No physical mass-gap claim. -/
namespace YangMills.RG
open Filter Module
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000

section Rescaling
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem curve_rescaled_tendsto (γ : ℝ → V) (v : V)
    (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = 0) :
    Tendsto (fun t : ℝ => t⁻¹ • γ t) (𝓝[≠] 0) (𝓝 v) := by
  simpa [hγ0] using hγ.tendsto_slope_zero

lemma regularSector_rescaled_norm_sq (t : ℝ) (x : V) :
    ‖t⁻¹ • x‖ ^ 2 = (t⁻¹) ^ 2 * ‖x‖ ^ 2 := by
  simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
end Rescaling

section Quadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularSector_rescaled_quadratic (T : E →L[ℝ] E) (t : ℝ) (x : E) :
    inner ℝ (t⁻¹ • x) (T (t⁻¹ • x)) = (t⁻¹) ^ 2 * inner ℝ x (T x) := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem quadratic_curve_rescaled_tendsto (T : E →L[ℝ] E)
    (γ : ℝ → E) (v : E) (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = 0) :
    Tendsto (fun t : ℝ => inner ℝ (t⁻¹ • γ t) (T (t⁻¹ • γ t)))
      (𝓝[≠] 0) (𝓝 (inner ℝ v (T v))) := by
  have hu := curve_rescaled_tendsto γ v hγ hγ0
  exact hu.inner (T.continuous.tendsto.comp hu)
end Quadratic

section Sector
variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem regular_sector_local_coercivity_false
    (S : Submodule ℝ E) (P : E → G) (A : E →L[ℝ] G)
    (hP : ContDiffAt ℝ 1 P 0) (hdP : HasFDerivAt P A 0)
    (hP0 : P 0 = 0) (hA : Function.Surjective A)
    (C : E → F) (L : E →L[ℝ] F) (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (T : E →L[ℝ] E) (Phi : F → ℝ) (K delta r b c : ℝ)
    (hdelta : 0 < delta) (hr : 0 < r)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hband : ∀ x : E, x ∈ S → inner ℝ x (T x) ≤ b * ‖x‖ ^ 2)
    (hdim : finrank ℝ F + finrank ℝ G < finrank ℝ S) (hbc : b < c) :
    ¬ ∀ x : E, P x = 0 → ‖x‖ < r →
      c * ‖x‖ ^ 2 ≤ inner ℝ x (T x) + Phi (C x) := by
  intro hbound
  rcases exists_unseen_regular_sector_curve S P A hP hdP hP0 hA C L hC hdim with
    ⟨v, hvS, hv, γ, hγ0, hγ, hlevel, hCγ⟩
  let u : ℝ → E := fun t => t⁻¹ • γ t
  let z : ℝ → F := fun t => t⁻¹ • C (γ t)
  have hu : Tendsto u (𝓝[≠] 0) (𝓝 v) := curve_rescaled_tendsto γ v hγ hγ0
  have hz : Tendsto z (𝓝[≠] 0) (𝓝 (0 : F)) := by
    simpa [z, Function.comp_def, hγ0, hC0] using
      curve_rescaled_tendsto (C ∘ γ) 0 hCγ (by simp [Function.comp_def, hγ0, hC0])
  have hnorm : Tendsto (fun t : ℝ => ‖γ t‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa [hγ0] using hγ.continuousAt.tendsto.norm
  have hCnorm : Tendsto (fun t : ℝ => ‖C (γ t)‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def, hγ0, hC0] using hCγ.continuousAt.tendsto.norm
  have hball : ∀ᶠ t : ℝ in 𝓝 0, ‖γ t‖ < r := (tendsto_order.mp hnorm).2 r hr
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖C (γ t)‖ < delta :=
    (tendsto_order.mp hCnorm).2 delta hdelta
  have hineq : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      c * ‖u t‖ ^ 2 ≤ inner ℝ (u t) (T (u t)) + K * ‖z t‖ ^ 2 := by
    filter_upwards [hlevel.filter_mono nhdsWithin_le_nhds,
      hball.filter_mono nhdsWithin_le_nhds,
      hsmall.filter_mono nhdsWithin_le_nhds] with t htP htball htdelta
    have hb : c * ‖γ t‖ ^ 2 ≤ inner ℝ (γ t) (T (γ t)) + K * ‖C (γ t)‖ ^ 2 :=
      (hbound _ htP htball).trans (add_le_add_left (hPhi _ htdelta) _)
    dsimp only [u, z]
    calc
      c * ‖t⁻¹ • γ t‖ ^ 2 = (t⁻¹) ^ 2 * (c * ‖γ t‖ ^ 2) := by
        rw [regularSector_rescaled_norm_sq]; ring
      _ ≤ (t⁻¹) ^ 2 * (inner ℝ (γ t) (T (γ t)) + K * ‖C (γ t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = inner ℝ (t⁻¹ • γ t) (T (t⁻¹ • γ t)) + K * ‖t⁻¹ • C (γ t)‖ ^ 2 := by
        rw [regularSector_rescaled_quadratic, regularSector_rescaled_norm_sq]; ring
  have hl : Tendsto (fun t : ℝ => c * ‖u t‖ ^ 2) (𝓝[≠] 0)
      (𝓝 (c * ‖v‖ ^ 2)) := tendsto_const_nhds.mul (hu.norm.pow 2)
  have hq : Tendsto (fun t : ℝ => inner ℝ (u t) (T (u t))) (𝓝[≠] 0)
      (𝓝 (inner ℝ v (T v))) := hu.inner (T.continuous.tendsto.comp hu)
  have hright := hq.add (tendsto_const_nhds.mul (hz.norm.pow 2))
  have hcv : c * ‖v‖ ^ 2 ≤ inner ℝ v (T v) := by
    simpa using le_of_tendsto_of_tendsto hl hright hineq
  have hstrict : b * ‖v‖ ^ 2 < c * ‖v‖ ^ 2 :=
    mul_lt_mul_of_pos_right hbc (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact (not_le_of_gt hstrict) (hcv.trans (hband v hvS))
end Sector

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F G : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem physicalBand_regular_sector_local_coercivity_false
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (j : Fin d) (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex d n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ p, w p ≤ M)
    (P : PhysicalGaugeOneCochain d n Nc → G)
    (A : PhysicalGaugeOneCochain d n Nc →L[ℝ] G)
    (hP : ContDiffAt ℝ 1 P 0) (hdP : HasFDerivAt P A 0)
    (hP0 : P 0 = 0) (hA : Function.Surjective A)
    (C : PhysicalGaugeOneCochain d n Nc → F)
    (L : PhysicalGaugeOneCochain d n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta r c : ℝ) (hdelta : 0 < delta) (hr : 0 < r)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hdim : finrank ℝ F + finrank ℝ G < 2 * (2 * R + 1) ^ d)
    (hc : (1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) < c) :
    ¬ ∀ x : PhysicalGaugeOneCochain d n Nc, P x = 0 → ‖x‖ < r →
      c * ‖x‖ ^ 2 ≤ inner ℝ x (flatGaugeHodgeK0CLM d n Nc rho x) +
        inner ℝ x (componentwiseWeightedRepairCLM w x) + Phi (C x) := by
  have hband : ∀ x : PhysicalGaugeOneCochain d n Nc,
      x ∈ physicalCenteredFourierBand (n := n) hNc j R →
      inner ℝ x ((flatGaugeHodgeK0CLM d n Nc rho + componentwiseWeightedRepairCLM w) x) ≤
        ((1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2)) * ‖x‖ ^ 2 := by
    intro x hx
    have hv := componentwiseWeightedRepair_le_hodge rho w M hw x
    have hb := physicalCenteredFourierBand_hodge_le hNc rho j R hR x hx
    simp only [ContinuousLinearMap.add_apply, inner_add_right]
    calc
      _ ≤ (1 + M) * inner ℝ x (flatGaugeHodgeK0CLM d n Nc rho x) := by nlinarith
      _ ≤ (1 + M) * ((4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 /
          (n : ℝ) ^ 2) * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = _ := by ring
  have hdim' : finrank ℝ F + finrank ℝ G <
      finrank ℝ (physicalCenteredFourierBand (n := n) hNc j R) := by
    simpa only [physicalCenteredFourierBand_finrank hNc j R hR] using hdim
  have hno := regular_sector_local_coercivity_false
    (physicalCenteredFourierBand (n := n) hNc j R) P A hP hdP hP0 hA C L hC hC0
    (flatGaugeHodgeK0CLM d n Nc rho + componentwiseWeightedRepairCLM w) Phi K delta r
    ((1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2)) c
    hdelta hr hPhi hband hdim' hc
  simpa only [ContinuousLinearMap.add_apply, inner_add_right] using hno
end Physical
end YangMills.RG
