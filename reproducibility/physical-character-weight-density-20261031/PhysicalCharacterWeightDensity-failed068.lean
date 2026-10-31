import YangMills.RG.TorusPhysicalHodge
import YangMills.RG.ComponentwiseFlatGradient

/-! Exact spatial energy density of actual physical character fields.
No weight bound, positivity or supplied density certificate is assumed.
The compressed-trace/rank step remains a separate obligation. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

section Character
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem character_amplitude_forward_density (chi : AddChar G ℂ)
    (z : ℂ) (a x : G) :
    ‖z * chi (x + a) - z * chi x‖ ^ 2 =
      ‖z‖ ^ 2 * ‖chi a - 1‖ ^ 2 := by
  rw [← mul_sub, character_forward_difference, norm_mul, norm_mul,
    AddChar.norm_apply]
  ring
end Character

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def physicalCharacterField (hNc : 2 ≤ Nc) (j : Fin d)
    (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ) :
    PhysicalGaugeOneCochain d n Nc :=
  torusPhysicalEmbed hNc j (fun x => z * chi x)

theorem physicalCharacter_gradient_density (hNc : 2 ≤ Nc) (j : Fin d)
    (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ)
    (i : Fin d) (x : FinBox d n) (l : Fin d) :
    ‖componentwiseFlatGradientCLM (physicalCharacterField hNc j chi z) (i,(x,l))‖ ^ 2 =
      if l = j then ‖z‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 else 0 := by
  classical
  rw [componentwiseFlatGradient_apply]
  by_cases hl : l = j
  · subst l
    have hp (y : FinBox d n) : physicalCharacterField hNc j chi z (y,j) =
        sunComplexPlane hNc (z * chi (finBoxZModEquiv d n y)) := by
      simp [physicalCharacterField, torusPhysicalEmbed]
    simp only [hp, if_pos rfl]
    rw [← sunComplexPlane_sub, sunComplexPlane_norm_sq, finBoxZModEquiv_shift]
    exact character_amplitude_forward_density chi z _ _
  · simp [physicalCharacterField, torusPhysicalEmbed, hl]

theorem physicalCharacter_norm_sq (hNc : 2 ≤ Nc) (j : Fin d)
    (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ) :
    ‖physicalCharacterField hNc j chi z‖ ^ 2 = (n : ℝ)^d * ‖z‖ ^ 2 := by
  rw [physicalCharacterField, torusPhysicalEmbed_norm_sq]
  simp [countingL2Mass, norm_mul, AddChar.norm_apply, nsmul_eq_mul]

theorem physicalCharacter_weightedRepair_energy (hNc : 2 ≤ Nc) (j : Fin d)
    (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ)
    (w : PhysicalGradientIndex d n → ℝ) :
    inner ℝ (physicalCharacterField hNc j chi z)
      (componentwiseWeightedRepairCLM w (physicalCharacterField hNc j chi z)) =
      ∑ i : Fin d, (‖z‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) *
        ∑ x : FinBox d n, w (i,(x,j)) := by
  classical
  rw [componentwiseWeightedRepair_energy]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hd (x : FinBox d n) (l : Fin d) :
      ‖physicalCharacterField hNc j chi z (x.shift i,l) -
        physicalCharacterField hNc j chi z (x,l)‖ ^ 2 =
      if l = j then ‖z‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 else 0 :=
    physicalCharacter_gradient_density hNc j chi z i x l
  simp_rw [hd]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem physicalCharacter_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (j : Fin d) (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ)
    (hj : chi (Pi.single j (1 : ZMod n)) = 1) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc)
      (physicalCharacterField hNc j chi z) = 0 := by
  apply PiLp.ext
  intro x
  rw [physicalCharacterField, torusPhysicalEmbed_flat_div_apply]
  have hc : chi (finBoxZModEquiv d n x - Pi.single j (1 : ZMod n)) =
      chi (finBoxZModEquiv d n x) := by
    have h := AddChar.map_add_eq_mul chi
      (finBoxZModEquiv d n x - Pi.single j (1 : ZMod n)) (Pi.single j (1 : ZMod n))
    simpa only [sub_add_cancel, hj, mul_one] using h.symm
  rw [hc, sub_self]
  simp [sunComplexPlane]

theorem physicalCharacter_hodge_energy (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (j : Fin d) (chi : AddChar (Fin d → ZMod n) ℂ) (z : ℂ) :
    inner ℝ (physicalCharacterField hNc j chi z)
      (flatGaugeHodgeK0CLM d n Nc rho (physicalCharacterField hNc j chi z)) =
      (n : ℝ)^d * ∑ i : Fin d,
        ‖z‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  classical
  rw [physicalCharacterField, torusPhysicalEmbed_flat_hodge_eq_stencil,
    oneComponentStencilEnergy_eq]
  simp_rw [forwardShiftEnergy, character_amplitude_forward_density]
  simp [nsmul_eq_mul, Finset.mul_sum]
end Physical
end YangMills.RG
