import YangMills.RG.PositiveCompressedTrace
import YangMills.RG.PhysicalTransverseCharacterStrip
import YangMills.RG.NonlinearTangentCoercivity

/-! Actual finite transverse-strip average-weight rank inequality. Local nonlinear
coercivity is differentiated along actual kernel directions; no supplied kernel
coercivity, band dimension, orthonormality or compressed trace certificate. -/
namespace YangMills.RG
open Module Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1600000

section Local
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem local_derivative_kernel_quadratic_lower
    (S : Submodule ℝ E) (T : E →ₗ[ℝ] E)
    (C : E → F) (L : E →L[ℝ] F) (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hlocal : ∀ x : E, x ∈ S → ‖x‖ < radius →
      c * ‖x‖ ^ 2 ≤ inner ℝ x (T x) + Phi (C x))
    (v : E) (hvS : v ∈ S) (hLv : L v = 0) :
    c * ‖v‖ ^ 2 ≤ inner ℝ v (T v) := by
  by_cases hv : v = 0
  · simp [hv]
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let b : ℝ := inner ℝ v (T v) / ‖v‖ ^ 2
  have henergy (t : ℝ) : inner ℝ (t • v) (T (t • v)) = b * ‖t • v‖ ^ 2 := by
    have hn : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, hn]
    dsimp [b]
    field_simp [hnv]
    <;> ring
  let z : ℝ → ℝ := fun t => ‖t • v‖⁻¹ * ‖C (t • v)‖
  have hz : Tendsto z (𝓝 0) (𝓝 0) :=
    tangent_kernel_norm_ratio_tendsto C L hC hC0 v hLv
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : E)) := by
    simpa using (tendsto_id.smul tendsto_const_nhds :
      Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)))
  have hn : Tendsto (fun t : ℝ => ‖C (t • v)‖) (𝓝 0) (𝓝 0) := by
    simpa [hC0] using (hC.continuousAt.tendsto.comp ht).norm
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖C (t • v)‖ < delta :=
    (tendsto_order.mp hn).2 delta hdelta
  have hball : ∀ᶠ t : ℝ in 𝓝 0, ‖t • v‖ < radius := by
    have hn0 : Tendsto (fun t : ℝ => ‖t • v‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using ht.norm
    exact (tendsto_order.mp hn0).2 radius hradius
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t htne
    exact htne
  have hge : ∀ᶠ t : ℝ in 𝓝[≠] 0, c ≤ b + K * (z t) ^ 2 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hball.filter_mono nhdsWithin_le_nhds, hne] with t htnear htball htne
    have htv : t • v ≠ 0 := smul_ne_zero htne hv
    have hnorm : ‖t • v‖ ≠ 0 := norm_ne_zero_iff.mpr htv
    have hpos : 0 < ‖t • v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr htv)
    have heq : ‖C (t • v)‖ ^ 2 = (z t) ^ 2 * ‖t • v‖ ^ 2 := by
      dsimp [z]
      field_simp
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      c * ‖t • v‖ ^ 2 ≤ inner ℝ (t • v) (T (t • v)) + Phi (C (t • v)) :=
        hlocal _ (S.smul_mem t hvS) htball
      _ ≤ b * ‖t • v‖ ^ 2 + K * ‖C (t • v)‖ ^ 2 := by
        rw [henergy]
        exact add_le_add_left (hPhi _ htnear) _
      _ = (b + K * (z t) ^ 2) * ‖t • v‖ ^ 2 := by rw [heq]; ring
  have hz' : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hz.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun t : ℝ => b + K * (z t) ^ 2) (𝓝[≠] 0)
      (𝓝 (b + K * (0 : ℝ) ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hz'.pow 2))
  have hcb : c ≤ b := by simpa using ge_of_tendsto hg hge
  have h := mul_le_mul_of_nonneg_right hcb (sq_nonneg ‖v‖)
  simpa [b, div_mul_cancel₀ _ (pow_ne_zero 2 hnv)] using h

theorem local_nonlinear_compressed_trace_rank_bound
    (S : Submodule ℝ E) (T : E →ₗ[ℝ] E)
    (hpos : ∀ x : E, x ∈ S → 0 ≤ inner ℝ x (T x))
    (C : E → F) (L : E →L[ℝ] F) (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 ≤ c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hlocal : ∀ x : E, x ∈ S → ‖x‖ < radius →
      c * ‖x‖ ^ 2 ≤ inner ℝ x (T x) + Phi (C x)) :
    c * ((finrank ℝ S : ℝ) - (finrank ℝ F : ℝ)) ≤
      LinearMap.trace ℝ S (finiteSubspaceCompression S T) := by
  apply positive_compressed_trace_rank_bound S T hpos L.toLinearMap c hc
  intro v hv hLv
  exact local_derivative_kernel_quadratic_lower S T C L hC hC0 Phi K delta radius c
    hdelta hradius hPhi hlocal v hv hLv

noncomputable def orthonormalSpanBasis {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : Orthonormal ℝ v) :
    OrthonormalBasis ι ℝ (Submodule.span ℝ (Set.range v)) := by
  classical
  let b := Basis.span hv.linearIndependent
  apply b.toOrthonormalBasis
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℝ (b i : E) (b j : E) = _
  simpa only [b, Basis.coe_span_apply] using (orthonormal_iff_ite.mp hv i j)

theorem orthonormalSpanBasis_coe {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : Orthonormal ℝ v) (i : ι) :
    (orthonormalSpanBasis v hv i : E) = v i := by
  classical
  simp [orthonormalSpanBasis]
end Local

section Physical
variable {d n Nc R : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def physicalTransverseStripSpace (hNc : 2 ≤ Nc) (i j : Fin d) (R : ℕ) :
    Submodule ℝ (PhysicalGaugeOneCochain d n Nc) :=
  Submodule.span ℝ (Set.range (fun p : Fin R × Bool =>
    normalizedTransversePhysicalCharacter (n := n) hNc i j p.1 p.2))

noncomputable def physicalFlatWeightedOperator (rho : SUNAdjointModel Nc)
    (w : PhysicalGradientIndex d n → ℝ) :
    PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] PhysicalGaugeOneCochain d n Nc :=
  (flatGaugeHodgeK0CLM d n Nc rho + componentwiseWeightedRepairCLM w).toLinearMap

theorem physicalTransverseStripSpace_div_zero (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
    (A : PhysicalGaugeOneCochain d n Nc)
    (hA : A ∈ physicalTransverseStripSpace hNc i j R) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc) A = 0 := by
  have hs : physicalTransverseStripSpace hNc i j R ≤
      LinearMap.ker (gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact normalizedTransversePhysicalCharacter_div_zero hNc rho i j hij p.1 p.2
  exact hs hA

theorem physicalFlatWeightedOperator_nonneg (rho : SUNAdjointModel Nc)
    (w : PhysicalGradientIndex d n → ℝ) (hw : ∀ p, 0 ≤ w p)
    (A : PhysicalGaugeOneCochain d n Nc) :
    0 ≤ inner ℝ A (physicalFlatWeightedOperator rho w A) := by
  change 0 ≤ inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A + componentwiseWeightedRepairCLM w A)
  rw [inner_add_right]
  exact add_nonneg (flatGaugeHodgeK0_nonnegative_right rho A)
    (componentwiseWeightedRepair_nonneg w hw A)

theorem physicalStripCompression_trace (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (i j : Fin d) (hR : R < n) (w : PhysicalGradientIndex d n → ℝ) :
    LinearMap.trace ℝ (physicalTransverseStripSpace hNc i j R)
      (finiteSubspaceCompression (physicalTransverseStripSpace hNc i j R)
        (physicalFlatWeightedOperator rho w)) =
      2 * (1 + physicalDirectionalWeightAverage w i j) *
        ∑ r : Fin R, ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 := by
  classical
  let v := fun p : Fin R × Bool => normalizedTransversePhysicalCharacter (n := n) hNc i j p.1 p.2
  let hv := normalizedTransversePhysicalCharacters_orthonormal hNc i j hR
  let b := orthonormalSpanBasis v hv
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [finiteSubspaceCompression_inner, orthonormalSpanBasis_coe, b]
  change (∑ p : Fin R × Bool, inner ℝ (v p)
    (flatGaugeHodgeK0CLM d n Nc rho (v p) + componentwiseWeightedRepairCLM w (v p))) = _
  simp_rw [inner_add_right]
  exact normalizedTransversePhysicalCharacters_energy_sum hNc rho i j w

theorem physicalStrip_nonlinear_average_rank_bound (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j) (hR : R < n)
    (w : PhysicalGradientIndex d n → ℝ) (hw : ∀ p, 0 ≤ w p)
    (C : PhysicalGaugeOneCochain d n Nc → F)
    (L : PhysicalGaugeOneCochain d n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 ≤ c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hlocal : ∀ A : PhysicalGaugeOneCochain d n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖ ^ 2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)) :
    c * (2 * (R : ℝ) - (finrank ℝ F : ℝ)) ≤
      2 * (1 + physicalDirectionalWeightAverage w i j) *
        ∑ r : Fin R, ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2 := by
  have h := local_nonlinear_compressed_trace_rank_bound
    (physicalTransverseStripSpace hNc i j R) (physicalFlatWeightedOperator rho w)
    (fun A _ => physicalFlatWeightedOperator_nonneg rho w hw A)
    C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi (by
      intro A hA hball
      have ha := hlocal A (physicalTransverseStripSpace_div_zero hNc rho i j hij A hA) hball
      change c * ‖A‖ ^ 2 ≤ inner ℝ A
        (flatGaugeHodgeK0CLM d n Nc rho A + componentwiseWeightedRepairCLM w A) + Phi (C A)
      simpa only [inner_add_right] using ha)
  rw [physicalStripCompression_trace hNc rho i j hR w] at h
  have hdim := normalizedTransversePhysicalCharacters_span_finrank (n := n) hNc i j hR
  change finrank ℝ (physicalTransverseStripSpace hNc i j R) = 2 * R at hdim
  simpa only [hdim, Nat.cast_mul, Nat.cast_ofNat] using h
end Physical
end YangMills.RG
