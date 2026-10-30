import YangMills.RG.PhysicalFourierRankObstruction
import YangMills.RG.ComponentwiseFlatHodge

/-! Nonlinear observations differentiated at zero and a locally upper-quadratic
penalty. The final endpoint uses the actual physical Fourier band and actual
weighted derivative repair. No topological zero theorem is assumed here. -/
namespace YangMills.RG
open Module Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000

section Tangent
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem tangent_kernel_norm_ratio_tendsto
    (C : E → F) (L : E →L[ℝ] F) (hC : HasFDerivAt C L 0)
    (hC0 : C 0 = 0) (v : E) (hv : L v = 0) :
    Tendsto (fun t : ℝ => ‖t • v‖⁻¹ * ‖C (t • v)‖) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
    simpa using (tendsto_id.smul tendsto_const_nhds :
      Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)))
  have hh := (hasFDerivAt_iff_tendsto.mp hC).comp ht
  simpa [Function.comp_def, hC0, map_smul, hv] using hh

theorem nonlinear_tangent_coercivity_false
    (S : Submodule ℝ E) (C : E → F) (L : E →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (energy : E → ℝ) (Phi : F → ℝ) (K delta b c : ℝ)
    (hdelta : 0 < delta)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hband : ∀ x : E, x ∈ S → energy x ≤ b * ‖x‖ ^ 2)
    (hdim : finrank ℝ F < finrank ℝ S) (hbc : b < c) :
    ¬ ∀ x : E, c * ‖x‖ ^ 2 ≤ energy x + Phi (C x) := by
  intro hbound
  have hd : finrank ℝ F + finrank ℝ (LinearMap.range (0 : E →ₗ[ℝ] E)) <
      finrank ℝ S := by
    simpa only [LinearMap.range_zero, finrank_bot, add_zero] using hdim
  rcases exists_unseen_of_finrank_lt_measurement_add_repair
    S L.toLinearMap (0 : E →ₗ[ℝ] E) hd with ⟨v, hvS, hv, hLv, _⟩
  let r : ℝ → ℝ := fun t => ‖t • v‖⁻¹ * ‖C (t • v)‖
  have hr : Tendsto r (𝓝 0) (𝓝 0) :=
    tangent_kernel_norm_ratio_tendsto C L hC hC0 v hLv
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
    simpa using (tendsto_id.smul tendsto_const_nhds :
      Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)))
  have hn : Tendsto (fun t : ℝ => ‖C (t • v)‖) (𝓝 0) (𝓝 0) := by
    simpa [hC0] using (hC.continuousAt.tendsto.comp ht).norm
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖C (t • v)‖ < delta :=
    (tendsto_order.mp hn).2 delta hdelta
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hge : ∀ᶠ t : ℝ in 𝓝[≠] 0, c ≤ b + K * (r t) ^ 2 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hne] with t ht htne
    have htv : t • v ≠ 0 := smul_ne_zero htne hv
    have hnorm : ‖t • v‖ ≠ 0 := norm_ne_zero_iff.mpr htv
    have hpos : 0 < ‖t • v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr htv)
    have heq : ‖C (t • v)‖ ^ 2 = (r t) ^ 2 * ‖t • v‖ ^ 2 := by
      dsimp [r]
      field_simp
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      c * ‖t • v‖ ^ 2 ≤ energy (t • v) + Phi (C (t • v)) := hbound _
      _ ≤ b * ‖t • v‖ ^ 2 + K * ‖C (t • v)‖ ^ 2 :=
        add_le_add (hband _ (S.smul_mem t hvS)) (hPhi _ ht)
      _ = (b + K * (r t) ^ 2) * ‖t • v‖ ^ 2 := by rw [heq]; ring
  have hr' := hr.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun t : ℝ => b + K * (r t) ^ 2) (𝓝[≠] 0)
      (𝓝 (b + K * (0 : ℝ) ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hr'.pow 2))
  have hcb : c ≤ b := by simpa using ge_of_tendsto hg hge
  exact (not_le_of_gt hbc) hcb
end Tangent

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ F]

theorem physicalBand_nonlinear_tangent_coercivity_false
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (j : Fin d)
    (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex d n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ p, w p ≤ M)
    (C : PhysicalGaugeOneCochain d n Nc → F)
    (L : PhysicalGaugeOneCochain d n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta c : ℝ) (hdelta : 0 < delta)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hdim : finrank ℝ F < 2 * (2 * R + 1) ^ d)
    (hc : (1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 /
      (n : ℝ) ^ 2) < c) :
    ¬ ∀ A : PhysicalGaugeOneCochain d n Nc,
      c * ‖A‖ ^ 2 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A) := by
  apply nonlinear_tangent_coercivity_false
    (physicalCenteredFourierBand (n := n) hNc j R) C L hC hC0
    (fun A => inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM w A)) Phi K delta
    ((1 + M) * (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2)) c
    hdelta hPhi
  · intro A hA
    have hv := componentwiseWeightedRepair_le_hodge rho w M hw A
    have hb := physicalCenteredFourierBand_hodge_le hNc rho j R hR A hA
    calc
      _ ≤ (1 + M) * inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) := by nlinarith
      _ ≤ (1 + M) * ((4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 /
          (n : ℝ) ^ 2) * ‖A‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = _ := by ring
  · simpa only [physicalCenteredFourierBand_finrank hNc j R hR] using hdim
  · exact hc
end Physical
end YangMills.RG
