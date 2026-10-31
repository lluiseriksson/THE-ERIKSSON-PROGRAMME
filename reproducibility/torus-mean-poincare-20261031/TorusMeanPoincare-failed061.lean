import YangMills.RG.CyclicMeanPoincare

/-! Actual finite-group averaging and a quantitative multidimensional torus
comparison. No spectral gap or desired Poincare certificate is assumed. -/
namespace YangMills.RG
open scoped BigOperators

section FiniteGroup
variable {G V : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def finiteArithmeticMean (f : PeriodicL2 G V) : V :=
  (Fintype.card G : ℝ)⁻¹ • ∑ x : G, f x

noncomputable def finiteMeanField (f : PeriodicL2 G V) : PeriodicL2 G V :=
  WithLp.toLp 2 (fun _ => finiteArithmeticMean f)

theorem finiteTranslationAverage_eq_mean (f : PeriodicL2 G V) :
    (Fintype.card G : ℝ)⁻¹ • ∑ a : G, periodicTranslate a f = finiteMeanField f := by
  classical
  apply PiLp.ext
  intro x
  have heval : (∑ a : G, periodicTranslate a f) x = ∑ a : G, f (x + a) :=
    map_sum (PiLp.projₗ (p := 2) (𝕜 := ℝ) (fun _ : G => V) x)
      (fun a => periodicTranslate a f) Finset.univ
  change (Fintype.card G : ℝ)⁻¹ • ((∑ a : G, periodicTranslate a f) x) =
    (Fintype.card G : ℝ)⁻¹ • ∑ y : G, f y
  rw [heval]
  congr 1
  exact Equiv.sum_comp (Equiv.addLeft x) (fun y => f y)

theorem finiteMean_norm_le_of_translate_bound (f : PeriodicL2 G V) (B : ℝ)
    (h : ∀ a : G, ‖periodicTranslate a f - f‖ ≤ B) :
    ‖f - finiteMeanField f‖ ≤ B := by
  classical
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn0 : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hf : (Fintype.card G : ℝ)⁻¹ • (∑ _a : G, f) = f := by
    simp only [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hd : f - finiteMeanField f =
      (Fintype.card G : ℝ)⁻¹ • ∑ a : G, (f - periodicTranslate a f) := by
    rw [Finset.sum_sub_distrib, smul_sub, hf, finiteTranslationAverage_eq_mean]
  rw [hd, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn0)]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ a : G, ‖f - periodicTranslate a f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn0)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _a : G, B := by
      gcongr with a
      simpa only [norm_sub_rev] using h a
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem periodicTranslate_difference_sum_le {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : PeriodicL2 G V) :
    ‖periodicTranslate (∑ i ∈ s, a i) f - f‖ ≤
      ∑ i ∈ s, ‖periodicTranslate (a i) f - f‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (periodicTranslate_difference_add_le (a i) (∑ j ∈ s, a j) f).trans
        (add_le_add le_rfl ih)
end FiniteGroup

section Torus
variable {D n : ℕ} [NeZero n] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def torusUnit (i : Fin D) : Fin D → ZMod n := Pi.single i 1

theorem torus_coordinate_decomposition (a : Fin D → ZMod n) :
    a = ∑ i : Fin D, (a i).val • torusUnit i := by
  classical
  ext j
  simp [torusUnit, Finset.sum_apply, Pi.single_apply]

theorem torusTranslate_difference_norm_le
    (a : Fin D → ZMod n) (f : PeriodicL2 (Fin D → ZMod n) V) :
    ‖periodicTranslate a f - f‖ ≤
      (n : ℝ) * ∑ i : Fin D, ‖periodicTranslate (torusUnit i) f - f‖ := by
  classical
  conv_lhs => rw [torus_coordinate_decomposition a]
  calc
    _ ≤ ∑ i : Fin D, ‖periodicTranslate ((a i).val • torusUnit i) f - f‖ :=
      periodicTranslate_difference_sum_le Finset.univ _ f
    _ ≤ ∑ i : Fin D, (n : ℝ) * ‖periodicTranslate (torusUnit i) f - f‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (periodicTranslate_difference_nsmul_le (torusUnit i) f (a i).val).trans
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_of_lt (ZMod.val_lt (a i))) (norm_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem torusMean_poincare_norm_le (f : PeriodicL2 (Fin D → ZMod n) V) :
    ‖f - finiteMeanField f‖ ≤
      (n : ℝ) * ∑ i : Fin D, ‖periodicTranslate (torusUnit i) f - f‖ :=
  finiteMean_norm_le_of_translate_bound f _ (fun a => torusTranslate_difference_norm_le a f)

theorem torusMean_poincare_energy_le (f : PeriodicL2 (Fin D → ZMod n) V) :
    (∑ x : Fin D → ZMod n, ‖f x - finiteArithmeticMean f‖ ^ 2) ≤
      (D : ℝ) * (n : ℝ) ^ 2 *
        ∑ i : Fin D, ∑ x : Fin D → ZMod n, ‖f (x + torusUnit i) - f x‖ ^ 2 := by
  classical
  have hs := pow_le_pow_left₀ (norm_nonneg (f - finiteMeanField f))
    (torusMean_poincare_norm_le f) 2
  have hc : (∑ i : Fin D, ‖periodicTranslate (torusUnit i) f - f‖) ^ 2 ≤
      (D : ℝ) * ∑ i : Fin D, ‖periodicTranslate (torusUnit i) f - f‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin D => (1 : ℝ)) (fun i => ‖periodicTranslate (torusUnit i) f - f‖)
  rw [mul_pow] at hs
  have ht := hs.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg (n : ℝ)))
  simp only [PiLp.norm_sq_eq_of_L2] at ht
  convert ht using 1 <;> ring
end Torus
end YangMills.RG
