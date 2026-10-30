import YangMills.RG.CoexactFlatBand
import YangMills.RG.TransverseFlatBand

/-! Actual disjoint-support norm and gradient splitting transports the Hodge
bound to the constructed volume-order coexact band. No comparison field. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000

theorem piLp_norm_sub_sq_of_disjoint {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    (A B : PiLp 2 E) (h : ∀ p, A p = 0 ∨ B p = 0) :
    ‖A - B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2 E (A - B), PiLp.norm_sq_eq_of_L2 E A,
    PiLp.norm_sq_eq_of_L2 E B, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change ‖A p - B p‖ ^ 2 = ‖A p‖ ^ 2 + ‖B p‖ ^ 2
  rcases h p with ha | hb
  · simp [ha]
  · simp [hb]

section Support
variable {D n Nc : ℕ} [NeZero D] [NeZero n] [NeZero Nc]

theorem torusPhysicalEmbed_disjoint (hNc : 2 ≤ Nc) (i j : Fin D) (hij : i ≠ j)
    (f g : (Fin D → ZMod n) → ℂ) (e : FinBox D n × Fin D) :
    torusPhysicalEmbed hNc i f e = 0 ∨ torusPhysicalEmbed hNc j g e = 0 := by
  classical
  by_cases hi : e.2 = i
  · right
    have hj : e.2 ≠ j := by simpa only [hi] using hij
    simp [torusPhysicalEmbed, hj]
  · left
    simp [torusPhysicalEmbed, hi]

theorem torusPhysicalEmbed_sub_norm_sq (hNc : 2 ≤ Nc) (i j : Fin D) (hij : i ≠ j)
    (f g : (Fin D → ZMod n) → ℂ) :
    ‖torusPhysicalEmbed hNc i f - torusPhysicalEmbed hNc j g‖ ^ 2 =
      ‖torusPhysicalEmbed hNc i f‖ ^ 2 + ‖torusPhysicalEmbed hNc j g‖ ^ 2 :=
  piLp_norm_sub_sq_of_disjoint _ _ (torusPhysicalEmbed_disjoint hNc i j hij f g)

theorem torusPhysicalEmbed_gradient_disjoint (hNc : 2 ≤ Nc) (i j : Fin D)
    (hij : i ≠ j) (f g : (Fin D → ZMod n) → ℂ) (p : PhysicalGradientIndex D n) :
    componentwiseFlatGradientCLM (torusPhysicalEmbed hNc i f) p = 0 ∨
      componentwiseFlatGradientCLM (torusPhysicalEmbed hNc j g) p = 0 := by
  classical
  by_cases hi : p.2.2 = i
  · right
    have hj : p.2.2 ≠ j := by simpa only [hi] using hij
    simp [componentwiseFlatGradient_apply, torusPhysicalEmbed, hj]
  · left
    simp [componentwiseFlatGradient_apply, torusPhysicalEmbed, hi]

theorem torusPhysicalEmbed_gradient_sub_norm_sq (hNc : 2 ≤ Nc) (i j : Fin D)
    (hij : i ≠ j) (f g : (Fin D → ZMod n) → ℂ) :
    ‖componentwiseFlatGradientCLM
      (torusPhysicalEmbed hNc i f - torusPhysicalEmbed hNc j g)‖ ^ 2 =
      ‖componentwiseFlatGradientCLM (torusPhysicalEmbed hNc i f)‖ ^ 2 +
        ‖componentwiseFlatGradientCLM (torusPhysicalEmbed hNc j g)‖ ^ 2 := by
  rw [map_sub]
  exact piLp_norm_sub_sq_of_disjoint _ _
    (torusPhysicalEmbed_gradient_disjoint hNc i j hij f g)

theorem torusPhysicalEmbed_hodge_sub_eq (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (i j : Fin D) (hij : i ≠ j) (f g : (Fin D → ZMod n) → ℂ) :
    inner ℝ (torusPhysicalEmbed hNc i f - torusPhysicalEmbed hNc j g)
      (flatGaugeHodgeK0CLM D n Nc rho
        (torusPhysicalEmbed hNc i f - torusPhysicalEmbed hNc j g)) =
      inner ℝ (torusPhysicalEmbed hNc i f)
        (flatGaugeHodgeK0CLM D n Nc rho (torusPhysicalEmbed hNc i f)) +
      inner ℝ (torusPhysicalEmbed hNc j g)
        (flatGaugeHodgeK0CLM D n Nc rho (torusPhysicalEmbed hNc j g)) := by
  rw [← componentwiseFlatGradient_eq_hodge rho,
    torusPhysicalEmbed_gradient_sub_norm_sq hNc i j hij,
    componentwiseFlatGradient_eq_hodge rho, componentwiseFlatGradient_eq_hodge rho]
end Support

section Scalar
variable {D n : ℕ} [NeZero n]

theorem centeredFourierProfile_backward_difference (R : ℕ)
    (k : Fin D → Fin (2 * R + 1)) (j : Fin D) :
    torusBackwardDifference j (centeredFourierProfile (n := n) R k) =
      (1 - centeredFourierProfile (n := n) R k (-Pi.single j (1 : ZMod n))) •
        centeredFourierProfile (n := n) R k := by
  funext x
  let e : Fin D → ZMod n := Pi.single j (1 : ZMod n)
  have hs : centeredFourierProfile (n := n) R k (x - e) -
      centeredFourierProfile (n := n) R k x =
      (centeredFourierProfile (n := n) R k (-e) - 1) *
        centeredFourierProfile (n := n) R k x := by
    simpa only [sub_eq_add_neg] using
      character_forward_difference (torusFourierCharacter (centeredFourierFrequency R k)) (-e) x
  change centeredFourierProfile R k x - centeredFourierProfile R k (x - e) =
    (1 - centeredFourierProfile R k (-e)) * centeredFourierProfile R k x
  linear_combination -hs

theorem centeredFourierBand_backward_mem (R : ℕ) (j : Fin D)
    (f : (Fin D → ZMod n) → ℂ) (hf : f ∈ centeredFourierBand D n R) :
    torusBackwardDifference j f ∈ centeredFourierBand D n R := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf with ⟨c, hc⟩
  rw [← hc, map_sum]
  apply Submodule.sum_mem
  intro k hk
  rw [map_smul, centeredFourierProfile_backward_difference]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem coexactPositiveScalarBand_le_centered {d : ℕ} (R : ℕ) :
    coexactPositiveScalarBand d n R ≤ centeredFourierBand (d + 2) n R := by
  apply Submodule.span_le.mpr
  rintro f ⟨k, rfl⟩
  exact Submodule.subset_span ⟨coexactPositiveFourierIndex R k, rfl⟩
end Scalar

section Energy
variable {D n Nc : ℕ} [NeZero D] [NeZero n] [NeZero Nc]

theorem coexactFlatMap_hodge_le (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (i j : Fin D) (hij : i ≠ j) (R : ℕ) (hR : 2 * R < n)
    (f : (Fin D → ZMod n) → ℂ) (hf : f ∈ centeredFourierBand D n R) :
    inner ℝ (coexactFlatMap hNc i j f)
      (flatGaugeHodgeK0CLM D n Nc rho (coexactFlatMap hNc i j f)) ≤
      (4 * Real.pi ^ 2 * (D : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) *
        ‖coexactFlatMap hNc i j f‖ ^ 2 := by
  have hi := physicalCenteredFourierBand_hodge_le hNc rho i R hR
    (torusPhysicalEmbed hNc i (torusBackwardDifference j f))
    ⟨⟨torusBackwardDifference j f, centeredFourierBand_backward_mem R j f hf⟩, rfl⟩
  have hj := physicalCenteredFourierBand_hodge_le hNc rho j R hR
    (torusPhysicalEmbed hNc j (torusBackwardDifference i f))
    ⟨⟨torusBackwardDifference i f, centeredFourierBand_backward_mem R i f hf⟩, rfl⟩
  rw [coexactFlatMap_apply, torusPhysicalEmbed_hodge_sub_eq hNc rho i j hij,
    torusPhysicalEmbed_sub_norm_sq hNc i j hij]
  nlinarith
end Energy

section PositiveEnergy
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem coexactPositivePhysicalBand_hodge_le (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (hR : 2 * R < n) (x : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hx : x ∈ coexactPositivePhysicalBand hNc R) :
    inner ℝ x (flatGaugeHodgeK0CLM (d + 2) n Nc rho x) ≤
      (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖x‖ ^ 2 := by
  rcases hx with ⟨f, rfl⟩
  exact coexactFlatMap_hodge_le hNc rho 0 (Fin.succ 0) (by simp) R hR f.val
    (coexactPositiveScalarBand_le_centered R f.property)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem coexactFlat_local_coercivity_false
    (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex (d + 2) n → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ p, w p ≤ M)
    (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta r c : ℝ) (hdelta : 0 < delta) (hr : 0 < r)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hdim : finrank ℝ F < 2 * R * (2 * R + 1) ^ (d + 1))
    (hc : (1 + M) * (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
      (n : ℝ) ^ 2) < c) :
    ¬ ∀ x : PhysicalGaugeOneCochain (d + 2) n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) x = 0 →
      ‖x‖ < r → c * ‖x‖ ^ 2 ≤ inner ℝ x (flatGaugeHodgeK0CLM (d + 2) n Nc rho x) +
        inner ℝ x (componentwiseWeightedRepairCLM w x) + Phi (C x) := by
  intro hbound
  have hband : ∀ x ∈ coexactPositivePhysicalBand (d := d) (n := n) hNc R,
      inner ℝ x (flatGaugeHodgeK0CLM (d + 2) n Nc rho x) +
        inner ℝ x (componentwiseWeightedRepairCLM w x) ≤
      ((1 + M) * (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
        (n : ℝ) ^ 2)) * ‖x‖ ^ 2 := by
    intro x hx
    have hv := componentwiseWeightedRepair_le_hodge rho w M hw x
    have hb := coexactPositivePhysicalBand_hodge_le hNc rho R hR x hx
    calc
      _ ≤ (1 + M) * inner ℝ x (flatGaugeHodgeK0CLM (d + 2) n Nc rho x) := by nlinarith
      _ ≤ (1 + M) * ((4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
        (n : ℝ) ^ 2) * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = _ := by ring
  have hdim' : finrank ℝ F <
      finrank ℝ (coexactPositivePhysicalBand (d := d) (n := n) hNc R) := by
    simpa only [coexactPositivePhysicalBand_finrank hNc R hR] using hdim
  have hno := nonlinear_tangent_local_subspace_coercivity_false
    (coexactPositivePhysicalBand (d := d) (n := n) hNc R) C L hC hC0
    (fun x => inner ℝ x (flatGaugeHodgeK0CLM (d + 2) n Nc rho x) +
      inner ℝ x (componentwiseWeightedRepairCLM w x)) Phi K delta r
    ((1 + M) * (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2)) c
    hdelta hr hPhi hband hdim' hc
  apply hno
  intro x hx hxr
  exact hbound x (coexactPositivePhysicalBand_div_zero hNc rho R x hx) hxr
end PositiveEnergy
end YangMills.RG
