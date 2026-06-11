/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Trace of a matrix product as a sum over index paths (area law, TE)

`docs/AREA-LAW-PLAN.md` §4, brick TE: the entry of an ordered product
of matrices is the sum over index paths of the products of the
traversed entries, and the trace of the product is the sum over
**closed** paths:

    tr(M₀ ⬝ ⋯ ⬝ M_{L-1}) = ∑_{closed index paths k} ∏ᵢ (Mᵢ)_{kᵢ, kᵢ₊₁}.

Applied to a Wilson loop, the matrices are the (oriented) edge
holonomies along the loop; each closed-path summand is a product of
single matrix entries of the traversed edges — a per-edge entry
monomial, which is exactly what the Haar balance criterion
(`sunHaarProb_fundMonomial_integral_zero`, AL3) consumes.  The
recursive `pathSum` form is chosen over a `Fin L → ι` indexed sum
precisely so the downstream induction (peeling one loop edge at a
time) is structural.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- The **path sum** of a list of matrices between two indices: the
sum over all index paths from `i` to `j` of the products of the
traversed entries.  Empty list: the Kronecker delta. -/
def pathSum : List (Matrix ι ι R) → ι → ι → R
  | [], i, j => if i = j then 1 else 0
  | M :: l, i, j => ∑ k, M i k * pathSum l k j

@[simp] theorem pathSum_nil (i j : ι) :
    pathSum ([] : List (Matrix ι ι R)) i j = if i = j then 1 else 0 :=
  rfl

@[simp] theorem pathSum_cons (M : Matrix ι ι R) (l : List (Matrix ι ι R))
    (i j : ι) :
    pathSum (M :: l) i j = ∑ k, M i k * pathSum l k j :=
  rfl

/-- **Entries of an ordered matrix product are path sums.** -/
theorem list_prod_apply (l : List (Matrix ι ι R)) (i j : ι) :
    l.prod i j = pathSum l i j := by
  induction l generalizing i with
  | nil => simp [List.prod_nil, Matrix.one_apply]
  | cons M l ih =>
    rw [List.prod_cons, pathSum_cons]
    show (M * l.prod) i j = _
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [ih k]

/-- **The trace of an ordered matrix product is the sum over closed
index paths** — the Wilson-loop form of the entry expansion. -/
theorem trace_list_prod_eq_sum_pathSum (l : List (Matrix ι ι R)) :
    Matrix.trace l.prod = ∑ i, pathSum l i i := by
  unfold Matrix.trace
  exact Finset.sum_congr rfl fun i _ => by
    rw [Matrix.diag_apply, list_prod_apply]

end YangMills
