/-
S-2a: transport of the cross-ratio bound under two-sided nonnegative mixing.

The paper *Congruence Rigidity and the Fusion Bound* proves that Hilbert's
projective diameter is invariant under positive **diagonal** congruence, and
leaves open what happens beyond that.  The answer is that it is **monotone**, and
the statement is not about congruence and not about symmetry:

    Δ(A M B) ≤ Δ(M)   for A, B entrywise nonnegative.

This module is the algebraic core, S-2a.  It carries no `log`, no division and no
metric: the whole content is that the family of bilinear inequalities defining
the diameter is closed under a nonnegative change of weights.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The cross-ratio bound transports under nonnegative mixing

`CrossRatioLB φ T` is the house orientation already used by
`YangMills/OS/CongruenceSpectrum.lean` (`BirkhoffInterface`,
`crossRatio_le_of_bounds`): `φ` is a lower bound for every cross-ratio of `T`,
written multiplicatively so that no division occurs.

The theorem is one index swap.  Expanding `(A M B)_{ik} (A M B)_{jl}` and
`(A M B)_{jk} (A M B)_{il}` produces the **same** nonnegative weights
`A_{ia} A_{jc} B_{bk} B_{dl}`, against `M_{ab} M_{cd}` in the first case and
`M_{cb} M_{ad}` in the second: renaming the summation indices `a ↔ c` in the
second expansion returns its coefficient to the first one's and moves the swap
onto the `M`-factors.  The hypothesis then applies termwise, and nonnegativity
of the weights carries it through the sum.
-/

namespace YangMills.OS

namespace Congruence

open Finset

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- **`φ` bounds every cross-ratio of `T` from below**, multiplicatively.  Same
orientation as `BirkhoffInterface` in `CongruenceSpectrum`, so the two compose
without a translation step. -/
def CrossRatioLB {r c : Type*} (φ : ℝ) (T : Matrix r c ℝ) : Prop :=
  ∀ (i j : r) (k l : c), φ * (T j k * T i l) ≤ T i k * T j l

/-- The triple product, expanded to a double sum. -/
theorem triple_apply (A : Matrix m n ℝ) (M : Matrix n n ℝ) (B : Matrix n p ℝ)
    (i : m) (k : p) :
    (A * M * B) i k = ∑ a : n, ∑ b : n, A i a * M a b * B b k := by
  rw [Matrix.mul_apply]
  have hb : ∀ b : n, (A * M) i b * B b k = ∑ a : n, A i a * M a b * B b k := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_comm]

/-- The product of two entries, as a single sum over quadruples, with the weight
factored out.  This is the identity the whole proof rests on. -/
theorem triple_mul_expand (A : Matrix m n ℝ) (M : Matrix n n ℝ) (B : Matrix n p ℝ)
    (i j : m) (k l : p) :
    (A * M * B) i k * (A * M * B) j l
      = ∑ a : n, ∑ b : n, ∑ c : n, ∑ d : n,
          (A i a * A j c * B b k * B d l) * (M a b * M c d) := by
  rw [triple_apply, triple_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The *same* weights, against the swapped `M`-factors.  Obtained from
`triple_mul_expand` by renaming `a ↔ c` and `b ↔ d`, which is a relabelling of
the summation and therefore free. -/
theorem triple_mul_expand_swap (A : Matrix m n ℝ) (M : Matrix n n ℝ)
    (B : Matrix n p ℝ) (i j : m) (k l : p) :
    (A * M * B) j k * (A * M * B) i l
      = ∑ a : n, ∑ b : n, ∑ c : n, ∑ d : n,
          (A i a * A j c * B b k * B d l) * (M c b * M a d) := by
  rw [triple_mul_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **S-2a.  The cross-ratio bound transports under two-sided nonnegative
mixing.**  No symmetry of `M`, no relation between `A` and `B`, no positivity of
`A` or `B` beyond nonnegativity, and no division anywhere. -/
theorem crossRatioLB_mul {φ : ℝ} {A : Matrix m n ℝ} {M : Matrix n n ℝ}
    {B : Matrix n p ℝ} (hA : ∀ i a, 0 ≤ A i a) (hB : ∀ b k, 0 ≤ B b k)
    (hM : CrossRatioLB φ M) : CrossRatioLB φ (A * M * B) := by
  intro i j k l
  rw [triple_mul_expand_swap, triple_mul_expand, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have hw : 0 ≤ A i a * A j c * B b k * B d l :=
    mul_nonneg (mul_nonneg (mul_nonneg (hA i a) (hA j c)) (hB b k)) (hB d l)
  have hterm : φ * (M c b * M a d) ≤ M a b * M c d := hM a c b d
  calc φ * ((A i a * A j c * B b k * B d l) * (M c b * M a d))
      = (A i a * A j c * B b k * B d l) * (φ * (M c b * M a d)) := by ring
    _ ≤ (A i a * A j c * B b k * B d l) * (M a b * M c d) :=
        mul_le_mul_of_nonneg_left hterm hw

/-- **Corollary: congruence.**  `B = Aᵀ` is the case the previous paper asked
about, and it is a special case rather than the theorem. -/
theorem crossRatioLB_congr {φ : ℝ} {S : Matrix m n ℝ} {M : Matrix n n ℝ}
    (hS : ∀ i a, 0 ≤ S i a) (hM : CrossRatioLB φ M) :
    CrossRatioLB φ (S * M * S.transpose) :=
  crossRatioLB_mul hS (fun b k => hS k b) hM

end Congruence

end YangMills.OS
