import YangMills.RG.RegularSectorCoercivity

/-! A constructed low band in the kernel of the actual flat divergence.
The first bond component has Fourier frequency zero in that direction.
No divergence-free-band hypothesis or bounded constraint-output dimension
is supplied. This remains a finite flat unit-spacing statement. -/
namespace YangMills.RG
open Module Filter
open scoped BigOperators Topology RealInnerProductSpace
set_option maxHeartbeats 1200000

section Fourier
variable {d n : ℕ} [NeZero n]

def transverseFourierIndex (R : ℕ) (k : Fin d → Fin (2 * R + 1)) :
    Fin (d + 1) → Fin (2 * R + 1) :=
  Fin.cons ⟨R, by omega⟩ k

theorem transverseFourierIndex_injective (R : ℕ) :
    Function.Injective (transverseFourierIndex (d := d) R) := by
  intro k l h
  funext i
  have hi := congrFun h i.succ
  simpa [transverseFourierIndex] using hi

noncomputable def transverseFourierProfile (R : ℕ) (k : Fin d → Fin (2 * R + 1)) :
    (Fin (d + 1) → ZMod n) → ℂ :=
  centeredFourierProfile R (transverseFourierIndex R k)

theorem transverseFourierProfiles_linearIndependent (R : ℕ) (hR : 2 * R < n) :
    LinearIndependent ℂ (transverseFourierProfile (d := d) (n := n) R) := by
  exact (centeredFourierProfiles_linearIndependent (d := d + 1) R hR).comp _
    (transverseFourierIndex_injective R)

noncomputable def transverseFourierBand (d n R : ℕ) [NeZero n] :
    Submodule ℂ ((Fin (d + 1) → ZMod n) → ℂ) :=
  Submodule.span ℂ (Set.range (transverseFourierProfile (d := d) (n := n) R))

theorem transverseFourierBand_finrank_complex (R : ℕ) (hR : 2 * R < n) :
    finrank ℂ (transverseFourierBand d n R) = (2 * R + 1) ^ d := by
  rw [transverseFourierBand,
    finrank_span_eq_card (transverseFourierProfiles_linearIndependent R hR)]
  simp

theorem transverseFourierBand_finrank_real (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (transverseFourierBand d n R) = 2 * (2 * R + 1) ^ d := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (transverseFourierBand d n R),
    Complex.finrank_real_complex, transverseFourierBand_finrank_complex R hR]

theorem transverseFourierBand_le_centered (R : ℕ) :
    transverseFourierBand d n R ≤ centeredFourierBand (d + 1) n R := by
  apply Submodule.span_le.mpr
  rintro f ⟨k, rfl⟩
  exact Submodule.subset_span ⟨transverseFourierIndex R k, rfl⟩

theorem transverseFourierProfile_shift (R : ℕ) (k : Fin d → Fin (2 * R + 1))
    (x : Fin (d + 1) → ZMod n) :
    transverseFourierProfile R k (x - Pi.single 0 (1 : ZMod n)) =
      transverseFourierProfile R k x := by
  classical
  change ZMod.stdAddChar (∑ i, centeredFourierFrequency R (transverseFourierIndex R k) i *
    (x - Pi.single 0 (1 : ZMod n)) i) =
    ZMod.stdAddChar (∑ i, centeredFourierFrequency R (transverseFourierIndex R k) i * x i)
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = 0
  · subst i
    simp [centeredFourierFrequency, transverseFourierIndex]
  · simp [Pi.sub_apply, Pi.single_apply, h, Ne.symm h]

theorem transverseFourierBand_shift (R : ℕ)
    (f : (Fin (d + 1) → ZMod n) → ℂ) (hf : f ∈ transverseFourierBand d n R)
    (x : Fin (d + 1) → ZMod n) :
    f (x - Pi.single 0 (1 : ZMod n)) = f x := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf with ⟨c, hc⟩
  have hs : f = fun y => ∑ k, c k * transverseFourierProfile R k y := by
    rw [← hc]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transverseFourierProfile_shift]
end Fourier

section Physical
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def transversePhysicalBandMap (hNc : 2 ≤ Nc) (R : ℕ) :
    transverseFourierBand d n R →ₗ[ℝ] PhysicalGaugeOneCochain (d + 1) n Nc where
  toFun f := torusPhysicalEmbed hNc 0 f.val
  map_add' f g := torusPhysicalEmbed_add hNc 0 f.val g.val
  map_smul' r f := torusPhysicalEmbed_smul hNc 0 r f.val

theorem transversePhysicalBandMap_injective (hNc : 2 ≤ Nc) (R : ℕ) :
    Function.Injective (transversePhysicalBandMap (d := d) (n := n) hNc R) := by
  intro f g h
  apply Subtype.ext
  exact torusPhysicalEmbed_injective hNc 0 h

noncomputable def transversePhysicalBand (hNc : 2 ≤ Nc) (R : ℕ) :
    Submodule ℝ (PhysicalGaugeOneCochain (d + 1) n Nc) :=
  LinearMap.range (transversePhysicalBandMap hNc R)

theorem transversePhysicalBand_finrank (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (transversePhysicalBand (d := d) (n := n) hNc R) =
      2 * (2 * R + 1) ^ d := by
  rw [transversePhysicalBand,
    LinearMap.finrank_range_of_inj (transversePhysicalBandMap_injective hNc R),
    transverseFourierBand_finrank_real R hR]

theorem transversePhysicalBand_le_centered (hNc : 2 ≤ Nc) (R : ℕ) :
    transversePhysicalBand (d := d) (n := n) hNc R ≤
      physicalCenteredFourierBand (d := d + 1) (n := n) hNc 0 R := by
  rintro x ⟨f, rfl⟩
  exact ⟨⟨f.val, transverseFourierBand_le_centered R f.property⟩, rfl⟩

theorem transversePhysicalBand_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (x : PhysicalGaugeOneCochain (d + 1) n Nc)
    (hx : x ∈ transversePhysicalBand hNc R) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 1) n Nc) x = 0 := by
  rcases hx with ⟨f, rfl⟩
  apply PiLp.ext
  intro y
  change gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 1) n Nc)
    (torusPhysicalEmbed hNc 0 f.val) y = 0
  rw [torusPhysicalEmbed_flat_div_apply, transverseFourierBand_shift R f.val f.property]
  simp [sunComplexPlane]

theorem transversePhysicalBand_hodge_le (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (hR : 2 * R < n) (x : PhysicalGaugeOneCochain (d + 1) n Nc)
    (hx : x ∈ transversePhysicalBand hNc R) :
    inner ℝ x (flatGaugeHodgeK0CLM (d + 1) n Nc rho x) ≤
      (4 * Real.pi ^ 2 * ((d + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖x‖ ^ 2 :=
  physicalCenteredFourierBand_hodge_le hNc rho 0 R hR x
    (transversePhysicalBand_le_centered hNc R hx)
end Physical

section LocalSubspace
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem nonlinear_tangent_local_subspace_coercivity_false
    (S : Submodule ℝ E) (C : E → F) (L : E →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (energy : E → ℝ) (Phi : F → ℝ) (K delta r b c : ℝ)
    (hdelta : 0 < delta) (hr : 0 < r)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hband : ∀ x : E, x ∈ S → energy x ≤ b * ‖x‖ ^ 2)
    (hdim : finrank ℝ F < finrank ℝ S) (hbc : b < c) :
    ¬ ∀ x : E, x ∈ S → ‖x‖ < r → c * ‖x‖ ^ 2 ≤ energy x + Phi (C x) := by
  classical
  intro hbound
  let f : S →ₗ[ℝ] F := L.toLinearMap.comp S.subtype
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hinj)
  have hex : ∃ x : S, x ≠ 0 ∧ f x = 0 := by
    by_contra hnone
    push_neg at hnone
    apply hnotinj
    intro x y hxy
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsub : x - y = 0 := by
      by_contra hne
      exact hnone (x - y) hne hz
    exact sub_eq_zero.mp hsub
  rcases hex with ⟨x, hx, hfx⟩
  let v : E := x
  have hvS : v ∈ S := x.property
  have hv : v ≠ 0 := by
    intro hz
    apply hx
    exact Subtype.ext hz
  have hLv : L v = 0 := by simpa [f, v] using hfx
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
  have hball : ∀ᶠ t : ℝ in 𝓝 0, ‖t • v‖ < r := by
    have hn0 : Tendsto (fun t : ℝ => ‖t • v‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using ht.norm
    exact (tendsto_order.mp hn0).2 r hr
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hge : ∀ᶠ t : ℝ in 𝓝[≠] 0, c ≤ b + K * (z t) ^ 2 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hball.filter_mono nhdsWithin_le_nhds, hne] with t ht htball htne
    have htv : t • v ≠ 0 := smul_ne_zero htne hv
    have hnorm : ‖t • v‖ ≠ 0 := norm_ne_zero_iff.mpr htv
    have hpos : 0 < ‖t • v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr htv)
    have heq : ‖C (t • v)‖ ^ 2 = (z t) ^ 2 * ‖t • v‖ ^ 2 := by
      dsimp [z]
      field_simp
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      c * ‖t • v‖ ^ 2 ≤ energy (t • v) + Phi (C (t • v)) :=
        hbound _ (S.smul_mem t hvS) htball
      _ ≤ b * ‖t • v‖ ^ 2 + K * ‖C (t • v)‖ ^ 2 :=
        add_le_add (hband _ (S.smul_mem t hvS)) (hPhi _ ht)
      _ = (b + K * (z t) ^ 2) * ‖t • v‖ ^ 2 := by rw [heq]; ring
  have hz' : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hz.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun t : ℝ => b + K * (z t) ^ 2) (𝓝[≠] 0)
      (𝓝 (b + K * (0 : ℝ) ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hz'.pow 2))
  have hcb : c ≤ b := by simpa using ge_of_tendsto hg hge
  exact (not_le_of_gt hbc) hcb
end LocalSubspace

section Obstruction
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem transverseFlat_local_coercivity_false
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex (d + 1) n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ p, w p ≤ M)
    (C : PhysicalGaugeOneCochain (d + 1) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 1) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta r c : ℝ) (hdelta : 0 < delta) (hr : 0 < r)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hdim : finrank ℝ F < 2 * (2 * R + 1) ^ d)
    (hc : (1 + M) * (4 * Real.pi ^ 2 * ((d + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
      (n : ℝ) ^ 2) < c) :
    ¬ ∀ x : PhysicalGaugeOneCochain (d + 1) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 1) n Nc) x = 0 →
      ‖x‖ < r → c * ‖x‖ ^ 2 ≤ inner ℝ x (flatGaugeHodgeK0CLM (d + 1) n Nc rho x) +
        inner ℝ x (componentwiseWeightedRepairCLM w x) + Phi (C x) := by
  intro hbound
  apply nonlinear_tangent_local_subspace_coercivity_false
    (transversePhysicalBand (d := d) (n := n) hNc R) C L hC hC0
    (fun x => inner ℝ x (flatGaugeHodgeK0CLM (d + 1) n Nc rho x) +
      inner ℝ x (componentwiseWeightedRepairCLM w x)) Phi K delta r
    ((1 + M) * (4 * Real.pi ^ 2 * ((d + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2)) c
    hdelta hr hPhi ?_ ?_ hc
  · intro x hx
    have hv := componentwiseWeightedRepair_le_hodge rho w M hw x
    have hb := transversePhysicalBand_hodge_le hNc rho R hR x hx
    calc
      _ ≤ (1 + M) * inner ℝ x (flatGaugeHodgeK0CLM (d + 1) n Nc rho x) := by nlinarith
      _ ≤ (1 + M) * ((4 * Real.pi ^ 2 * ((d + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
        (n : ℝ) ^ 2) * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = _ := by ring
  · simpa only [transversePhysicalBand_finrank hNc R hR] using hdim
  · intro x hx hxr
    exact hbound x (transversePhysicalBand_div_zero hNc rho R x hx) hxr
end Obstruction
end YangMills.RG
