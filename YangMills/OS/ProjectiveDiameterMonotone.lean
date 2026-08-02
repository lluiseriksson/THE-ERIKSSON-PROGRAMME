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

**The mixed matrix is described by its entries, not by the `*` notation.**  A
first attempt wrote `A * M * B`; with three independent index types that failed
to elaborate at every occurrence, and the failure was not incidental — the
theorem is genuinely a statement about the entrywise formula, so
`IsMixOf T A M B` says exactly that and the product notation never appears.  It
also lets the same theorem serve `A * M * B`, `S * M * Sᵀ` and any other object
whose entries have that shape, without a coercion step.

The theorem itself is one index swap.  Expanding `T_{ik} T_{jl}` and
`T_{jk} T_{il}` produces the **same** nonnegative weights
`A_{ia} A_{jc} B_{bk} B_{dl}`, against `M_{ab} M_{cd}` in the first case and
`M_{cb} M_{ad}` in the second: renaming the summation indices `a ↔ c` in the
second expansion returns its coefficient to the first one's and moves the swap
onto the `M`-factors.  The hypothesis then applies termwise, and nonnegativity
of the weights carries it through the sum.
-/

namespace YangMills.OS

namespace Congruence

open Finset

variable {m n p : Type*} [Fintype n]

/-- **`φ` bounds every cross-ratio of `T` from below**, multiplicatively.  Same
orientation as `BirkhoffInterface` in `CongruenceSpectrum`, so the two compose
without a translation step.  Its equality cases are therefore a *tight set* —
the quadruples attaining the **minimum** of the cross-ratio — and not the
`ArgMax` of that ratio. -/
def CrossRatioLB {r c : Type*} (φ : ℝ) (T : Matrix r c ℝ) : Prop :=
  ∀ (i j : r) (k l : c), φ * (T j k * T i l) ≤ T i k * T j l

/-- `T` is the two-sided mix of `M` by `A` and `B`, stated on entries. -/
def IsMixOf (T : Matrix m p ℝ) (A : Matrix m n ℝ) (M : Matrix n n ℝ)
    (B : Matrix n p ℝ) : Prop :=
  ∀ i k, T i k = ∑ a : n, ∑ b : n, A i a * M a b * B b k

/-- The product of two entries of a mix, as a quadruple sum with the weight
factored out.  This is the identity the whole proof rests on. -/
theorem mix_mul_expand {T : Matrix m p ℝ} {A : Matrix m n ℝ} {M : Matrix n n ℝ}
    {B : Matrix n p ℝ} (hT : IsMixOf T A M B) (i j : m) (k l : p) :
    T i k * T j l
      = ∑ a : n, ∑ b : n, ∑ c : n, ∑ d : n,
          (A i a * A j c * B b k * B d l) * (M a b * M c d) := by
  rw [hT i k, hT j l, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The *same* weights, against the swapped `M`-factors.  Obtained from
`mix_mul_expand` by relabelling the summation indices, which is free. -/
theorem mix_mul_expand_swap {T : Matrix m p ℝ} {A : Matrix m n ℝ} {M : Matrix n n ℝ}
    {B : Matrix n p ℝ} (hT : IsMixOf T A M B) (i j : m) (k l : p) :
    T j k * T i l
      = ∑ a : n, ∑ b : n, ∑ c : n, ∑ d : n,
          (A i a * A j c * B b k * B d l) * (M c b * M a d) := by
  rw [mix_mul_expand hT j i k l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **S-2a.  The cross-ratio bound transports under two-sided nonnegative
mixing.**  No symmetry of `M`, no relation between `A` and `B`, no positivity of
`A` or `B` beyond nonnegativity, no positivity of `M`, and no division anywhere.

Note what this does *not* say.  It transports **one fixed** `φ`.  The statement
about diameters is `φ(A M B) ≥ φ(M)` for the *optimal* bounds, which needs the
construction of that optimum and is a separate step. -/
theorem crossRatioLB_mix {φ : ℝ} {T : Matrix m p ℝ} {A : Matrix m n ℝ}
    {M : Matrix n n ℝ} {B : Matrix n p ℝ} (hT : IsMixOf T A M B)
    (hA : ∀ i a, 0 ≤ A i a) (hB : ∀ b k, 0 ≤ B b k) (hM : CrossRatioLB φ M) :
    CrossRatioLB φ T := by
  intro i j k l
  rw [mix_mul_expand_swap hT i j k l, mix_mul_expand hT i j k l, Finset.mul_sum]
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

/-- **Corollary: congruence.**  The case `B = Aᵀ`, which is what the previous
paper asked about — a special case rather than the theorem. -/
theorem crossRatioLB_congr {φ : ℝ} {T : Matrix m m ℝ} {S : Matrix m n ℝ}
    {M : Matrix n n ℝ} (hT : IsMixOf T S M S.transpose)
    (hS : ∀ i a, 0 ≤ S i a) (hM : CrossRatioLB φ M) : CrossRatioLB φ T :=
  crossRatioLB_mix hT hS (fun b k => hS k b) hM

end Congruence

end YangMills.OS
