import YangMills.RG.BalabanCMP116WeakenedRandomWalkSum
import Mathlib.Analysis.Normed.Group.FunctionSeries

#check Summable.of_norm_bounded
#check tendstoUniformlyOn_tsum
#check Finset.prod_le_pow_card
#check Finset.abs_prod
#check Summable.tsum_subtype_add_tsum_subtype_compl
#check tsum_subtype
#check HasSum.tsum_eq
#check Summable.hasSum
#check Summable.subtype
#check Summable.indicator
#check HasDerivAt.const_smul
#check HasDerivAt.smul_const
#check pow_le_pow_right₀
#check Summable.tsum_add
#check Summable.tsum_const_smul
#check HasDerivWithinAt.congr

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {Δ : Type u} {ω : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem test_bound (active : Finset Δ) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : ∀ d ∈ active, |s d| ≤ R) :
    |cmp116WeakeningMonomial active s| ≤ R ^ active.card := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [cmp116WeakeningMonomial]
  | @insert d active hd ih =>
      rw [cmp116WeakeningMonomial, Finset.prod_insert hd, abs_mul,
        Finset.card_insert_of_notMem hd, pow_succ]
      simpa [mul_comm] using mul_le_mul (hs d (Finset.mem_insert_self d active))
        (ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)))
        (abs_nonneg _) hR

noncomputable def testSeries (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) : E :=
  ∑' w, cmp116WeakeningMonomial (active w) s • term w

def testDisc (R : ℝ) : Set (Δ → ℝ) := {s | ∀ d, |s d| ≤ R}

theorem test_term_bound (active : Finset Δ) (term : E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ testDisc R) :
    ‖cmp116WeakeningMonomial active s • term‖ ≤ R ^ active.card * ‖term‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (test_bound active s R hR (fun d _ => hs d)) (norm_nonneg term)

theorem test_summable [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) :
    Summable fun w => cmp116WeakeningMonomial (active w) s • term w :=
  Summable.of_norm_bounded hmajor fun w => test_term_bound (active w) (term w) s R hR hs

theorem test_uniform [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (R : ℝ)
    (hR : 0 ≤ R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) :
    TendstoUniformlyOn
      (fun F : Finset ω => fun s =>
        ∑ w ∈ F, cmp116WeakeningMonomial (active w) s • term w)
      (testSeries active term) Filter.atTop (testDisc R) := by
  exact tendstoUniformlyOn_tsum hmajor fun w s hs =>
    test_term_bound (active w) (term w) s R hR hs

theorem test_one (active : ω → Finset Δ) (term : ω → E) :
    testSeries active term (fun _ => 1) = ∑' w, term w := by
  apply tsum_congr
  intro w
  simp [testSeries, cmp116WeakeningMonomial]

theorem test_hasSum [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) :
    HasSum (fun w => cmp116WeakeningMonomial (active w) s • term w)
      (testSeries active term s) := by
  exact (test_summable active term s R hR hs hmajor).hasSum

section Decidable
variable [DecidableEq Δ]

theorem test_zero (active : ω → Finset Δ) (term : ω → E) (K : Finset Δ) :
    testSeries active term (cmp116WeakeningZeroOutside K) =
      ∑' w : {w // active w ⊆ K}, term w := by
  rw [testSeries]
  calc
    (∑' w, cmp116WeakeningMonomial (active w) (cmp116WeakeningZeroOutside K) • term w) =
        ∑' w, Set.indicator {w | active w ⊆ K} term w := by
      apply tsum_congr
      intro w
      rw [Set.indicator_apply]
      by_cases h : active w ⊆ K
      · simp [h, cmp116WeakeningMonomial_zeroOutside]
      · simp [h, cmp116WeakeningMonomial_zeroOutside]
    _ = ∑' w : {w // active w ⊆ K}, term w :=
      (tsum_subtype {w | active w ⊆ K} term).symm

noncomputable def testDerivative (active : ω → Finset Δ) (term : ω → E)
    (s : Δ → ℝ) (d : Δ) : E :=
  ∑' w, (if d ∈ active w then
    cmp116WeakeningMonomial ((active w).erase d) s else 0) • term w

theorem test_derivative_summable [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) :
    Summable fun w => (if d ∈ active w then
      cmp116WeakeningMonomial ((active w).erase d) s else 0) • term w := by
  apply Summable.of_norm_bounded hmajor
  intro w
  by_cases hd : d ∈ active w
  · simp only [hd, if_true]
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (test_bound ((active w).erase d) s R (zero_le_one.trans hR)
      (fun x _ => hs x)).trans
        (pow_le_pow_right₀ hR Finset.card_erase_le)
  · simp [hd, mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (norm_nonneg _)]

theorem test_affine [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) (t : ℝ)
    (ht : |t| ≤ R) :
    testSeries active term (Function.update s d t) =
      t • testDerivative active term s d +
        testSeries active term (Function.update s d 0) := by
  let derivTerm : ω → E := fun w => (if d ∈ active w then
      cmp116WeakeningMonomial ((active w).erase d) s else 0) • term w
  let zeroTerm : ω → E := fun w =>
      cmp116WeakeningMonomial (active w) (Function.update s d 0) • term w
  have hsUpdate : Function.update s d t ∈ testDisc R := by
    intro x
    by_cases hx : x = d
    · subst x
      simpa using ht
    · rw [Function.update_of_ne hx]
      exact hs x
  have hsZero : Function.update s d 0 ∈ testDisc R := by
    intro x
    by_cases hx : x = d
    · subst x
      simp [zero_le_one.trans hR]
    · rw [Function.update_of_ne hx]
      exact hs x
  have hDeriv : Summable derivTerm :=
    test_derivative_summable active term s d R hR hs hmajor
  have hZero : Summable zeroTerm :=
    test_summable active term _ R (zero_le_one.trans hR) hsZero hmajor
  calc
    testSeries active term (Function.update s d t) =
        ∑' w, (t • derivTerm w + zeroTerm w) := by
      apply tsum_congr
      intro w
      by_cases hd : d ∈ active w
      · simp only [derivTerm, zeroTerm, hd, if_true]
        rw [cmp116WeakeningMonomial_update_of_mem (active w) s d hd t,
          cmp116WeakeningMonomial_update_of_mem (active w) s d hd 0]
        simp [testSeries, mul_smul]
      · simp only [derivTerm, zeroTerm, hd, if_false, zero_smul, zero_add]
        rw [cmp116WeakeningMonomial_update_of_not_mem (active w) s d hd t,
          cmp116WeakeningMonomial_update_of_not_mem (active w) s d hd 0]
        simp
    _ = (∑' w, t • derivTerm w) + ∑' w, zeroTerm w :=
      (hDeriv.const_smul t).tsum_add hZero
    _ = t • testDerivative active term s d +
        testSeries active term (Function.update s d 0) := by
      rw [hDeriv.tsum_const_smul]
      rfl

theorem test_hasDerivWithin [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖)
    (x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
    HasDerivWithinAt (fun t => testSeries active term (Function.update s d t))
      (testDerivative active term s d) (Set.Icc (-R) R) x := by
  have hbase : HasDerivWithinAt
      (fun t => t • testDerivative active term s d +
        testSeries active term (Function.update s d 0))
      (testDerivative active term s d) (Set.Icc (-R) R) x := by
    simpa using ((hasDerivAt_id x).smul_const (testDerivative active term s d) |>.add_const
      (testSeries active term (Function.update s d 0))).hasDerivWithinAt
  apply hbase.congr
  · intro t ht
    exact test_affine active term s d R hR hs hmajor t
      (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
  · exact test_affine active term s d R hR hs hmajor x
      (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)

theorem test_hasDerivAt [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 ≤ R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖)
    (x : ℝ) (hx : x ∈ Set.Ioo (-R) R) :
    HasDerivAt (fun t => testSeries active term (Function.update s d t))
      (testDerivative active term s d) x := by
  exact (test_hasDerivWithin active term s d R hR hs hmajor x
    (Set.Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

theorem test_ftc [CompleteSpace E]
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (R : ℝ)
    (hR : 1 < R) (hs : s ∈ testDisc R)
    (hmajor : Summable fun w => R ^ (active w).card * ‖term w‖) :
    testSeries active term (Function.update s d 0) +
        ∫ _t in (0 : ℝ)..1, testDerivative active term s d =
      testSeries active term (Function.update s d 1) := by
  apply cmp116FTC_oneStep
    (fun t => testSeries active term (Function.update s d t))
    (fun _ => testDerivative active term s d)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact test_hasDerivAt active term s d R hR.le hs hmajor t
      ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  · exact continuous_const.intervalIntegrable 0 1

end Decidable

end YangMills.RG
