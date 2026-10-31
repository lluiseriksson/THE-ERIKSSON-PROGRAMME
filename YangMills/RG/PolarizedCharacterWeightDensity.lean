import YangMills.RG.PhysicalCharacterWeightDensity

/-! Actual multi-component character energy. No orthonormal packet, coexact
polarization, compression trace or output-rank density is assumed or claimed
here. These identities are one transport step toward that construction. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def polarizedPhysicalCharacter (hNc : 2 ≤ Nc)
    (chi : AddChar (Fin d → ZMod n) ℂ) (p : Fin d → ℂ) :
    PhysicalGaugeOneCochain d n Nc :=
  WithLp.toLp 2 (fun e => sunComplexPlane hNc (p e.2 * chi (finBoxZModEquiv d n e.1)))

theorem polarizedCharacter_gradient_density (hNc : 2 ≤ Nc)
    (chi : AddChar (Fin d → ZMod n) ℂ) (p : Fin d → ℂ)
    (i : Fin d) (x : FinBox d n) (l : Fin d) :
    ‖componentwiseFlatGradientCLM (polarizedPhysicalCharacter hNc chi p) (i,(x,l))‖ ^ 2 =
      ‖p l‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  rw [componentwiseFlatGradient_apply]
  change ‖sunComplexPlane hNc (p l * chi (finBoxZModEquiv d n (x.shift i))) -
    sunComplexPlane hNc (p l * chi (finBoxZModEquiv d n x))‖ ^ 2 = _
  rw [← sunComplexPlane_sub, sunComplexPlane_norm_sq, finBoxZModEquiv_shift]
  exact character_amplitude_forward_density chi (p l) _ _

theorem polarizedCharacter_norm_sq (hNc : 2 ≤ Nc)
    (chi : AddChar (Fin d → ZMod n) ℂ) (p : Fin d → ℂ) :
    ‖polarizedPhysicalCharacter hNc chi p‖ ^ 2 = (n : ℝ)^d * ∑ l, ‖p l‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ e : FinBox d n × Fin d,
    ‖sunComplexPlane hNc (p e.2 * chi (finBoxZModEquiv d n e.1))‖ ^ 2) = _
  simp_rw [sunComplexPlane_norm_sq, norm_mul, AddChar.norm_apply]
  simp [Fintype.sum_prod_type, card_finBox, nsmul_eq_mul]

theorem polarizedCharacter_weightedRepair_energy (hNc : 2 ≤ Nc)
    (chi : AddChar (Fin d → ZMod n) ℂ) (p : Fin d → ℂ)
    (w : PhysicalGradientIndex d n → ℝ) :
    inner ℝ (polarizedPhysicalCharacter hNc chi p)
      (componentwiseWeightedRepairCLM w (polarizedPhysicalCharacter hNc chi p)) =
      ∑ i : Fin d, ∑ l : Fin d,
        (‖p l‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) *
          ∑ x : FinBox d n, w (i,(x,l)) := by
  classical
  rw [componentwiseWeightedRepair_energy]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hd (x : FinBox d n) (l : Fin d) :
      ‖polarizedPhysicalCharacter hNc chi p (x.shift i,l) -
        polarizedPhysicalCharacter hNc chi p (x,l)‖ ^ 2 =
        ‖p l‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 :=
    polarizedCharacter_gradient_density hNc chi p i x l
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem polarizedCharacter_mean_upper (hNc : 2 ≤ Nc)
    (chi : AddChar (Fin d → ZMod n) ℂ) (p : Fin d → ℂ)
    (w : PhysicalGradientIndex d n → ℝ) (M : ℝ)
    (hw : ∀ i l, ∑ x : FinBox d n, w (i,(x,l)) ≤ (n : ℝ)^d * M) :
    inner ℝ (polarizedPhysicalCharacter hNc chi p)
      (componentwiseWeightedRepairCLM w (polarizedPhysicalCharacter hNc chi p)) ≤
      ∑ i : Fin d, ∑ l : Fin d,
        (‖p l‖ ^ 2 * ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) * ((n : ℝ)^d * M) := by
  rw [polarizedCharacter_weightedRepair_energy]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ =>
    mul_le_mul_of_nonneg_left (hw i l) (mul_nonneg (sq_nonneg _) (sq_nonneg _))))
end YangMills.RG
