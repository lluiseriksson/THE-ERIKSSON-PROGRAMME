import YangMills.RG.BalabanCMP89Eq251AliasWeightRedistribution

/-!
# PRE-VALIDATION: bare inverse-Laplacian redistribution at exponent one half

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

This is the pointwise bridge for the unsmoothed diagonal branch below CMP89
(2.46).  Unlike the already sealed source-weight bridge, it does not assume an
averaging-amplitude factor.  Consequently the finite alias sum retains the
visible inverse-Laplacian value scale.
-/

namespace YangMills.RG

noncomputable section

/-- In four dimensions the bare inverse-Laplacian factor is at most nine
times the product alias weight of coordinate exponent `1/2`. -/
theorem cmp89Eq251BareInverseLaplacian_le_nine_mul_halfWeight
    {m : Fin 4 → ℤ} (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq251EuclideanNorm
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ^ (-(2 : ℝ)) ≤
      9 * cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m := by
  let q : Fin 4 → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let product : ℝ := ∏ mu,
    (1 + |2 * Real.pi * (m mu : ℝ)|) ^ (1 / 2 : ℝ)
  have hredistributed :=
    cmp89Eq251AliasExcessProduct_div_euclideanNorm_rpow_le
      (d := 4) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  norm_num [Real.rpow_two] at hredistributed
  have hproductPos : 0 < product := by
    dsimp [product]
    exact Finset.prod_pos fun mu _ => Real.rpow_pos_of_pos (by positivity) _
  have hnormPos : 0 < cmp89Eq251EuclideanNorm q := by
    exact Real.pi_pos.trans_le (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hscaled :
      1 / cmp89Eq251EuclideanNorm q ^ 2 ≤ 9 / product := by
    apply (le_div_iff₀ hproductPos).2
    simpa [q, product, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hredistributed
  have hweight :
      cmp89Eq251MultidimensionalAliasWeight (1 / 2 : ℝ) m = 1 / product := by
    simp [cmp89Eq251MultidimensionalAliasWeight,
      cmp89Eq251OneDimensionalAliasWeight, product, one_div,
      Finset.prod_inv_distrib]
  rw [Real.rpow_neg hnormPos.le, Real.rpow_two]
  rw [hweight]
  simpa [q, div_eq_mul_inv, mul_assoc] using hscaled

end

end YangMills.RG
