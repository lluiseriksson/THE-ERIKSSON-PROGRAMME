/-
  ParityBarrier.lean — machine-checked core of
  "Parity Barriers for Decoupling Inequalities" (L. Eriksson, July 2026, v4).
  PARAMETRIC-IN-r theorems (all n), plus independent `decide` kernel
  instances for r = 1..4. No sorry. Only Mathlib.
-/
import Mathlib

/-- The ±1 value of a Boolean coordinate. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The character `χ_S(x) = ∏_{i ∈ S} sgn (x i)`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  ∏ i ∈ S, sgn (x i)

/-- The even-parity support `{x : ∏_i sgn (x i) = 1}`. -/
def parityEven (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => chi Finset.univ x = 1)

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

lemma sgn_not (b : Bool) : sgn (!b) = - sgn b := by cases b <;> simp [sgn]

lemma chi_sq {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x * chi S x = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => sgn_sq (x i)

/-- Flipping a coordinate inside `S` flips the sign of `χ_S`. -/
lemma chi_update {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool)
    {i : Fin n} (hi : i ∈ S) :
    chi S (Function.update x i (!x i)) = - chi S x := by
  unfold chi
  rw [← Finset.mul_prod_erase S _ hi, ← Finset.mul_prod_erase S _ hi]
  have h1 : Function.update x i (!x i) i = !x i := Function.update_self ..
  have h2 : ∏ j ∈ S.erase i, sgn (Function.update x i (!x i) j)
      = ∏ j ∈ S.erase i, sgn (x j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1, h2, sgn_not, neg_mul]

/-- **Full-space character sum**: for nonempty `T`,
`∑_{x ∈ {±1}^n} χ_T(x) = 0`. -/
theorem sum_chi_eq_zero (n : ℕ) (T : Finset (Fin n)) (hT : T.Nonempty) :
    ∑ x : Fin n → Bool, chi T x = 0 := by
  classical
  obtain ⟨i, hi⟩ := hT
  have key : ∀ x : Fin n → Bool,
      chi T x + chi T (Function.update x i (!x i)) = 0 := by
    intro x; rw [chi_update T x hi]; ring
  have hinv : ∀ x : Fin n → Bool,
      Function.update (Function.update x i (!x i)) i
        (!(Function.update x i (!x i) i)) = x := by
    intro x
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self]
    · simp [Function.update_of_ne hj]
  -- pair each x with its flip at i
  refine Finset.sum_involution (fun x _ => Function.update x i (!x i))
    (fun x _ => key x)
    (fun x _ _ h => ?_)
    (fun x _ => Finset.mem_univ _)
    (fun x _ => hinv x)
  have hxi := congrFun h i
  simp only [Function.update_self] at hxi
  simp at hxi

/-- `χ_S · χ_univ = χ_{univ \ S}`. -/
lemma chi_mul_chi_univ {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x * chi Finset.univ x = chi (Finset.univ \ S) x := by
  have hu : (Finset.univ : Finset (Fin n)) = S ∪ (Finset.univ \ S) := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ S)]
  have hdisj : Disjoint S (Finset.univ \ S) := Finset.disjoint_sdiff
  calc chi S x * chi Finset.univ x
      = chi S x * (chi S x * chi (Finset.univ \ S) x) := by
        rw [show chi Finset.univ x = chi S x * chi (Finset.univ \ S) x from by
          unfold chi; rw [← Finset.prod_union hdisj, ← hu]]
    _ = (chi S x * chi S x) * chi (Finset.univ \ S) x := by ring
    _ = chi (Finset.univ \ S) x := by rw [chi_sq]; ring

/-- **Statement (a), parametric in `r` (Fourier form).** For every `n`
and every nonempty proper `S ⊆ [n]`, the character sum over the
even-parity support vanishes — i.e. the parity measure is
`(n−1)`-wise independent. -/
theorem parity_kwise (n : ℕ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    ∑ x ∈ parityEven n, chi S x = 0 := by
  classical
  have hcompl : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h => hSne (Finset.univ_subset_iff.mp h)
  -- 2 · Σ_{parity} χ_S = Σ_x χ_S (1 + χ_univ) = Σ χ_S + Σ χ_{univ\S} = 0
  have split : ∀ x : Fin n → Bool,
      (if chi Finset.univ x = 1 then chi S x else 0) * 2
        = chi S x + chi S x * chi Finset.univ x := by
    intro x
    have hpm : chi Finset.univ x = 1 ∨ chi Finset.univ x = -1 :=
      mul_self_eq_one_iff.mp (chi_sq (Finset.univ : Finset (Fin n)) x)
    rcases hpm with h | h
    · rw [if_pos h, h]; ring
    · rw [if_neg (by rw [h]; norm_num), h]; ring
  have lhs_eq : ∑ x ∈ parityEven n, chi S x
      = ∑ x : Fin n → Bool, (if chi Finset.univ x = 1 then chi S x else 0) := by
    rw [parityEven, Finset.sum_filter]
  have total : (∑ x ∈ parityEven n, chi S x) * 2
      = (∑ x : Fin n → Bool, chi S x)
        + ∑ x : Fin n → Bool, chi (Finset.univ \ S) x := by
    rw [lhs_eq, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [split x, chi_mul_chi_univ]
  rw [sum_chi_eq_zero n S hS, sum_chi_eq_zero n (Finset.univ \ S) hcompl] at total
  omega

/-- **Statement (b), parametric.** On the even-parity support the last
coordinate is the product of the others. -/
theorem parity_support (n : ℕ) (x : Fin (n+1) → Bool)
    (hx : x ∈ parityEven (n+1)) :
    sgn (x (Fin.last n)) =
      ∏ i ∈ Finset.univ.erase (Fin.last n), sgn (x i) := by
  have h1 : chi Finset.univ x = 1 := by
    simpa [parityEven] using hx
  have hsplit : chi Finset.univ x
      = sgn (x (Fin.last n)) * ∏ i ∈ Finset.univ.erase (Fin.last n), sgn (x i) := by
    unfold chi
    exact Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ _) |>.symm
  have h2 : sgn (x (Fin.last n)) * (sgn (x (Fin.last n))
      * ∏ i ∈ Finset.univ.erase (Fin.last n), sgn (x i))
      = sgn (x (Fin.last n)) * 1 := by
    rw [← hsplit, h1]
  rw [← mul_assoc, sgn_sq, one_mul, mul_one] at h2
  exact h2.symm

/- Independent kernel checks by exhaustive computation, r = 1..4. -/

theorem parity_kwise_r1 :
    ∀ S : Finset (Fin 2), S.Nonempty → S.card ≤ 1 →
      ∑ x ∈ parityEven 2, chi S x = 0 := by decide

theorem parity_kwise_r2 :
    ∀ S : Finset (Fin 3), S.Nonempty → S.card ≤ 2 →
      ∑ x ∈ parityEven 3, chi S x = 0 := by decide

theorem parity_kwise_r3 :
    ∀ S : Finset (Fin 4), S.Nonempty → S.card ≤ 3 →
      ∑ x ∈ parityEven 4, chi S x = 0 := by decide

theorem parity_kwise_r4 :
    ∀ S : Finset (Fin 5), S.Nonempty → S.card ≤ 4 →
      ∑ x ∈ parityEven 5, chi S x = 0 := by decide

theorem parity_support_r4 :
    ∀ x ∈ parityEven 5, sgn (x (Fin.last 4)) =
      ∏ i ∈ Finset.univ.erase (Fin.last 4), sgn (x i) := by decide

theorem parity_mean_zero_r4 :
    ∑ x ∈ parityEven 5, sgn (x (Fin.last 4)) = 0 := by decide

#print axioms sum_chi_eq_zero
#print axioms parity_kwise
#print axioms parity_support
#print axioms parity_kwise_r4
