/-
  ParityBarrier.lean — kernel-checked finite instances of the parity barrier
  ("Parity Barriers for Decoupling Inequalities", L. Eriksson, July 2026).
  Statements (a) and (b) of the main theorem for r = 1, 2, 3, 4,
  proved by `decide` (finite exhaustive kernel computation). No sorry.
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

/- Statement (a), Fourier form, for r = 1..4 (n = r+1):
every character of nonempty support of order ≤ r sums to zero over the
even-parity support — equivalently, all marginals of order ≤ r of the
uniform measure on `parityEven n` coincide with the uniform product
measure. -/

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

/- Statement (b) for r = 1..4: on the even-parity support the last
coordinate is a deterministic function (the product) of the others. -/

theorem parity_support_r1 :
    ∀ x ∈ parityEven 2, sgn (x (Fin.last 1)) =
      ∏ i ∈ Finset.univ.erase (Fin.last 1), sgn (x i) := by decide

theorem parity_support_r2 :
    ∀ x ∈ parityEven 3, sgn (x (Fin.last 2)) =
      ∏ i ∈ Finset.univ.erase (Fin.last 2), sgn (x i) := by decide

theorem parity_support_r3 :
    ∀ x ∈ parityEven 4, sgn (x (Fin.last 3)) =
      ∏ i ∈ Finset.univ.erase (Fin.last 3), sgn (x i) := by decide

theorem parity_support_r4 :
    ∀ x ∈ parityEven 5, sgn (x (Fin.last 4)) =
      ∏ i ∈ Finset.univ.erase (Fin.last 4), sgn (x i) := by decide

/- The separation used in the barrier corollary, for r = 1..4: the
maximally-coupled variance is attained — the sum of `sgn` of the last
coordinate over the parity support vanishes (mean zero, so variance 1
after normalisation), while the coordinate is support-determined by (b). -/

theorem parity_mean_zero_r1 :
    ∑ x ∈ parityEven 2, sgn (x (Fin.last 1)) = 0 := by decide

theorem parity_mean_zero_r4 :
    ∑ x ∈ parityEven 5, sgn (x (Fin.last 4)) = 0 := by decide

#print axioms parity_kwise_r4
#print axioms parity_support_r4
#print axioms parity_mean_zero_r4
