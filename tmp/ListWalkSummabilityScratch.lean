import YangMills.RG.BalabanCMP116WeakenedRandomWalkSeries
import Mathlib.Data.List.OfFn

#check summable_sigma_of_nonneg
#check summable_geometric_of_norm_lt_one
#check summable_geometric_iff_norm_lt_one
#check Equiv.summable_iff
#check Fintype.card_fun
#check List.equivSigmaTuple
#check Summable.of_nonneg_of_le
#check Summable.mul_left
#check Summable.of_finite

open scoped BigOperators

namespace YangMills.RG

variable {σ : Type*} [Fintype σ]

theorem summable_list_pow_length (q : ℝ) (hq : 0 ≤ q)
    (hsmall : Fintype.card σ * q < 1) :
    Summable fun walk : List σ => q ^ walk.length := by
  rw [← List.equivSigmaTuple.symm.summable_iff]
  rw [show ((fun walk : List σ => q ^ walk.length) ∘
      (List.equivSigmaTuple.symm : (Σ n, Fin n → σ) → List σ)) =
        (fun p : Σ n, Fin n → σ => q ^ p.1) by
    funext p
    rcases p with ⟨n, f⟩
    simp [List.equivSigmaTuple]]
  rw [summable_sigma_of_nonneg (fun p => pow_nonneg hq p.1)]
  constructor
  · intro n
    exact Summable.of_finite
  · have hgeom :=
      (summable_geometric_of_norm_lt_one (show ‖(Fintype.card σ : ℝ) * q‖ < 1 by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hq)]
        exact hsmall))
    simpa [Fintype.card_fun, mul_pow] using hgeom

section Active

variable {Δ : Type*}
variable [DecidableEq Δ]

def listActive (cube : σ → Δ) (walk : List σ) : Finset Δ :=
  (walk.map cube).toFinset

theorem listActive_card_le (cube : σ → Δ) (walk : List σ) :
    (listActive cube walk).card ≤ walk.length := by
  simpa using List.toFinset_card_le (walk.map cube)

variable {E : Type*} [NormedAddCommGroup E]

theorem test_majorant (cube : σ → Δ) (term : List σ → E) (R rho A : ℝ)
    (hR : 1 ≤ R) (hrho : 0 ≤ rho)
    (hsmall : (Fintype.card σ : ℝ) * (R * rho) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.length) :
    Summable fun walk : List σ =>
      R ^ (listActive cube walk).card * ‖term walk‖ := by
  have hgeom : Summable fun walk : List σ => (R * rho) ^ walk.length :=
    summable_list_pow_length (R * rho)
      (mul_nonneg (zero_le_one.trans hR) hrho) hsmall
  have hupper : Summable fun walk : List σ => A * (R * rho) ^ walk.length :=
    hgeom.mul_left A
  apply Summable.of_nonneg_of_le
  · intro walk
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (norm_nonneg _)
  · intro walk
    calc
      R ^ (listActive cube walk).card * ‖term walk‖ ≤
          R ^ walk.length * (A * rho ^ walk.length) :=
        mul_le_mul
          (pow_le_pow_right₀ hR (listActive_card_le cube walk))
          (hterm walk) (norm_nonneg _)
          (pow_nonneg (zero_le_one.trans hR) _)
      _ = A * (R * rho) ^ walk.length := by
        rw [mul_pow]
        ring
  · exact hupper

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem test_series_summable (cube : σ → Δ) (term : List σ → E)
    (s : Δ → ℝ) (R rho A : ℝ)
    (hR : 1 ≤ R) (hrho : 0 ≤ rho)
    (hsmall : (Fintype.card σ : ℝ) * (R * rho) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.length)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : List σ =>
      cmp116WeakeningMonomial (listActive cube walk) s • term walk := by
  exact summable_cmp116WeakenedRandomWalkSeries
    (listActive cube) term s R (zero_le_one.trans hR) hs
    (test_majorant cube term R rho A hR hrho hsmall hterm)

theorem test_series_uniform (cube : σ → Δ) (term : List σ → E)
    (R rho A : ℝ)
    (hR : 1 ≤ R) (hrho : 0 ≤ rho)
    (hsmall : (Fintype.card σ : ℝ) * (R * rho) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.length) :
    TendstoUniformlyOn
      (fun walks : Finset (List σ) => fun s =>
        ∑ walk ∈ walks,
          cmp116WeakeningMonomial (listActive cube walk) s • term walk)
      (cmp116WeakenedRandomWalkSeries (listActive cube) term)
      Filter.atTop (cmp116WeakeningPolydisc R) := by
  exact tendstoUniformlyOn_cmp116WeakenedRandomWalkSeries
    (listActive cube) term R (zero_le_one.trans hR)
    (test_majorant cube term R rho A hR hrho hsmall hterm)

theorem test_series_ftc (cube : σ → Δ) (term : List σ → E)
    (s : Δ → ℝ) (d : Δ) (R rho A : ℝ)
    (hR : 1 ≤ R) (hrho : 0 ≤ rho)
    (hsmall : (Fintype.card σ : ℝ) * (R * rho) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * rho ^ walk.length)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    cmp116WeakenedRandomWalkSeries (listActive cube) term
        (Function.update s d 0) +
      ∫ _t in (0 : ℝ)..1,
        cmp116WeakenedRandomWalkSeriesDerivative
          (listActive cube) term s d =
      cmp116WeakenedRandomWalkSeries (listActive cube) term
        (Function.update s d 1) := by
  exact cmp116WeakenedRandomWalkSeries_ftcStep
    (listActive cube) term s d R hR hs
    (test_majorant cube term R rho A hR hrho hsmall hterm)

end Active

end YangMills.RG
