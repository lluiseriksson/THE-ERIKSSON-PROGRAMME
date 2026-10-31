import Mathlib

/-! An actual counting-L2 Poincare estimate for normed-vector-valued fields on
a finite cycle. This derives a quadratic-size comparison from translations;
it does not assume a spectral gap or a Poincare certificate. -/
namespace YangMills.RG
open scoped BigOperators

abbrev PeriodicL2 (G V : Type*) [Fintype G] := PiLp 2 (fun _ : G => V)

section Translations
variable {G V : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def periodicTranslate (a : G) (f : PeriodicL2 G V) : PeriodicL2 G V :=
  WithLp.toLp 2 (fun x => f (x + a))

@[simp] theorem periodicTranslate_apply (a x : G) (f : PeriodicL2 G V) :
    periodicTranslate a f x = f (x + a) := rfl

@[simp] theorem periodicTranslate_zero (f : PeriodicL2 G V) :
    periodicTranslate 0 f = f := by
  apply PiLp.ext
  intro x
  simp

theorem periodicTranslate_norm (a : G) (f : PeriodicL2 G V) :
    ‖periodicTranslate a f‖ = ‖f‖ := by
  classical
  have hs : ‖periodicTranslate a f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    change (∑ x : G, ‖f (x + a)‖ ^ 2) = ∑ x : G, ‖f x‖ ^ 2
    exact Equiv.sum_comp (Equiv.addRight a) (fun x => ‖f x‖ ^ 2)
  have ha := (sq_eq_sq_iff_abs_eq_abs ‖periodicTranslate a f‖ ‖f‖).mp hs
  simpa only [abs_of_nonneg (norm_nonneg _)] using ha

theorem periodicTranslate_difference_add_le (a b : G) (f : PeriodicL2 G V) :
    ‖periodicTranslate (a + b) f - f‖ ≤
      ‖periodicTranslate a f - f‖ + ‖periodicTranslate b f - f‖ := by
  have heq : periodicTranslate (a + b) f - f =
      periodicTranslate a (periodicTranslate b f - f) + (periodicTranslate a f - f) := by
    apply PiLp.ext
    intro x
    change f (x + (a + b)) - f x =
      (f ((x + a) + b) - f (x + a)) + (f (x + a) - f x)
    rw [add_assoc]
    abel
  rw [heq]
  calc
    _ ≤ ‖periodicTranslate a (periodicTranslate b f - f)‖ +
        ‖periodicTranslate a f - f‖ := norm_add_le _ _
    _ = _ := by rw [periodicTranslate_norm]; ring

theorem periodicTranslate_difference_nsmul_le (a : G) (f : PeriodicL2 G V) (m : ℕ) :
    ‖periodicTranslate (m • a) f - f‖ ≤ (m : ℝ) * ‖periodicTranslate a f - f‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        _ ≤ ‖periodicTranslate (m • a) f - f‖ + ‖periodicTranslate a f - f‖ := by
          simpa only [add_nsmul, one_nsmul] using
            periodicTranslate_difference_add_le (m • a) a f
        _ ≤ (m : ℝ) * ‖periodicTranslate a f - f‖ + ‖periodicTranslate a f - f‖ :=
          add_le_add_right ih _
        _ = _ := by push_cast; ring
end Translations

section Cycle
variable {n : ℕ} [NeZero n] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def cyclicArithmeticMean (f : PeriodicL2 (ZMod n) V) : V :=
  (n : ℝ)⁻¹ • ∑ x : ZMod n, f x

noncomputable def cyclicMeanField (f : PeriodicL2 (ZMod n) V) : PeriodicL2 (ZMod n) V :=
  WithLp.toLp 2 (fun _ => cyclicArithmeticMean f)

theorem cyclicTranslationAverage_eq_mean (f : PeriodicL2 (ZMod n) V) :
    (n : ℝ)⁻¹ • (∑ a : ZMod n, periodicTranslate a f) = cyclicMeanField f := by
  classical
  apply PiLp.ext
  intro x
  have heval : (∑ a : ZMod n, periodicTranslate a f) x = ∑ a : ZMod n, f (x + a) :=
    map_sum (PiLp.projₗ (p := 2) (𝕜 := ℝ) x) (fun a => periodicTranslate a f) Finset.univ
  change (n : ℝ)⁻¹ • ((∑ a : ZMod n, periodicTranslate a f) x) =
    (n : ℝ)⁻¹ • ∑ y : ZMod n, f y
  rw [heval]
  congr 1
  exact Equiv.sum_comp (Equiv.addLeft x) (fun y => f y)

theorem cyclicMean_poincare_norm_le (f : PeriodicL2 (ZMod n) V) :
    ‖f - cyclicMeanField f‖ ≤ (n : ℝ) * ‖periodicTranslate (1 : ZMod n) f - f‖ := by
  classical
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf : (n : ℝ)⁻¹ • (∑ _a : ZMod n, f) = f := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hdiff : f - cyclicMeanField f =
      (n : ℝ)⁻¹ • ∑ a : ZMod n, (f - periodicTranslate a f) := by
    rw [Finset.sum_sub_distrib, smul_sub, hf, cyclicTranslationAverage_eq_mean]
  have hpoint (a : ZMod n) :
      ‖f - periodicTranslate a f‖ ≤
        (n : ℝ) * ‖periodicTranslate (1 : ZMod n) f - f‖ := by
    have ht := periodicTranslate_difference_nsmul_le (1 : ZMod n) f a.val
    have ha : a.val • (1 : ZMod n) = a := by
      simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    rw [ha] at ht
    rw [norm_sub_rev]
    exact ht.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt (ZMod.val_lt a)) (norm_nonneg _))
  rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn0)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ a : ZMod n, ‖f - periodicTranslate a f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn0)
    _ ≤ (n : ℝ)⁻¹ * ∑ _a : ZMod n,
        ((n : ℝ) * ‖periodicTranslate (1 : ZMod n) f - f‖) := by
      gcongr with a
      exact hpoint a
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      field_simp

theorem cyclicMean_poincare_energy_le (f : PeriodicL2 (ZMod n) V) :
    (∑ x : ZMod n, ‖f x - cyclicArithmeticMean f‖ ^ 2) ≤
      (n : ℝ) ^ 2 * ∑ x : ZMod n, ‖f (x + 1) - f x‖ ^ 2 := by
  have hs := pow_le_pow_left₀ (norm_nonneg (f - cyclicMeanField f))
    (cyclicMean_poincare_norm_le f) 2
  rw [mul_pow] at hs
  simp only [PiLp.norm_sq_eq_of_L2] at hs
  exact hs
end Cycle
end YangMills.RG
