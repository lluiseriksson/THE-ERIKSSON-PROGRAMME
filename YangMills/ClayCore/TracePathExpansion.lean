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

/-! ## TE-1b: the closed (`Fin`-indexed) vertex-sequence expansion

The recursive `pathSum` is the induction-friendly form; the per-edge
grouping (`prod_comp_eq_prod_fiber`) instead consumes a product over a
`Fin`-indexed position set.  This section provides the bridge: the
path sum as a sum over vertex sequences `v : Fin (L+1) → ι` with
delta-pinned endpoints, so that for each fixed `v` the factor at
position `idx` reads only the matrix `l.get idx`. -/

/-- **Closed form of the path sum.** -/
theorem pathSum_eq_sum_vertexSeq (l : List (Matrix ι ι R)) (i j : ι) :
    pathSum l i j
      = ∑ v : Fin (l.length + 1) → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last l.length) = j then (1 : R) else 0) *
              ∏ idx : Fin l.length,
                l.get idx (v idx.castSucc) (v idx.succ) := by
  induction l generalizing i with
  | nil =>
      rw [pathSum_nil]
      show _ = ∑ v : Fin 1 → ι,
        (if v 0 = i then (1 : R) else 0) *
          (if v (Fin.last 0) = j then (1 : R) else 0) *
            ∏ idx : Fin 0,
              ([] : List (Matrix ι ι R)).get idx (v idx.castSucc) (v idx.succ)
      have htrans : (∑ v : Fin 1 → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last 0) = j then (1 : R) else 0) *
              ∏ idx : Fin 0,
                ([] : List (Matrix ι ι R)).get idx (v idx.castSucc) (v idx.succ))
          = ∑ a : ι, (if a = i then (1 : R) else 0) *
              (if a = j then (1 : R) else 0) := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun v => ?_
        show (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last 0) = j then (1 : R) else 0) *
              ∏ idx : Fin 0, _ = _
        rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        rfl
      rw [htrans, Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
      · intro a _ ha
        rw [if_neg ha, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
  | cons M l ih =>
      rw [pathSum_cons]
      show _ = ∑ v : Fin (l.length + 1 + 1) → ι,
        (if v 0 = i then (1 : R) else 0) *
          (if v (Fin.last (l.length + 1)) = j then (1 : R) else 0) *
            ∏ idx : Fin (l.length + 1),
              (M :: l).get idx (v idx.castSucc) (v idx.succ)
      -- transport the RHS sum along `Fin.cons`
      have htrans : (∑ v : Fin (l.length + 1 + 1) → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last (l.length + 1)) = j then (1 : R) else 0) *
              ∏ idx : Fin (l.length + 1),
                (M :: l).get idx (v idx.castSucc) (v idx.succ))
          = ∑ p : ι × (Fin (l.length + 1) → ι),
              (if p.1 = i then (1 : R) else 0) *
                (if p.2 (Fin.last l.length) = j then (1 : R) else 0) *
                  (M p.1 (p.2 0) *
                    ∏ idx : Fin l.length,
                      l.get idx (p.2 idx.castSucc) (p.2 idx.succ)) := by
        refine (Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _
          fun p => ?_).symm
        simp only [Fin.consEquiv_apply]
        have hv0 : Fin.cons (α := fun _ => ι) p.1 p.2 0 = p.1 :=
          Fin.cons_zero _ _
        have hvlast : Fin.cons (α := fun _ => ι) p.1 p.2
            (Fin.last (l.length + 1)) = p.2 (Fin.last l.length) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have hprod : (∏ idx : Fin (l.length + 1),
            (M :: l).get idx
              (Fin.cons (α := fun _ => ι) p.1 p.2 idx.castSucc)
              (Fin.cons (α := fun _ => ι) p.1 p.2 idx.succ))
            = M p.1 (p.2 0) *
                ∏ idx : Fin l.length,
                  l.get idx (p.2 idx.castSucc) (p.2 idx.succ) := by
          rw [Fin.prod_univ_succ]
          congr 1
        simp only [hv0, hvlast, hprod]
      rw [htrans]
      -- both sides reduce to the same `w`-sum normal form
      have hL : (∑ k, M i k * pathSum l k j)
          = ∑ w : Fin (l.length + 1) → ι,
              (if w (Fin.last l.length) = j then (1 : R) else 0) *
                (M i (w 0) * ∏ idx : Fin l.length,
                  l.get idx (w idx.castSucc) (w idx.succ)) := by
        rw [Finset.sum_congr rfl fun k _ => by
          rw [ih k, Finset.mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_eq_single (w 0)]
        · rw [if_pos rfl, one_mul]
          ring
        · intro k _ hk
          rw [if_neg fun h => hk h.symm, zero_mul, zero_mul, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ (w 0)) h
      have hR : (∑ p : ι × (Fin (l.length + 1) → ι),
          (if p.1 = i then (1 : R) else 0) *
            (if p.2 (Fin.last l.length) = j then (1 : R) else 0) *
              (M p.1 (p.2 0) *
                ∏ idx : Fin l.length,
                  l.get idx (p.2 idx.castSucc) (p.2 idx.succ)))
          = ∑ w : Fin (l.length + 1) → ι,
              (if w (Fin.last l.length) = j then (1 : R) else 0) *
                (M i (w 0) * ∏ idx : Fin l.length,
                  l.get idx (w idx.castSucc) (w idx.succ)) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single i]
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [if_pos rfl, one_mul]
        · intro a _ ha
          refine Finset.sum_eq_zero fun w _ => ?_
          rw [if_neg ha, zero_mul, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [hR]
      exact hL

/-- **The trace as a sum over closed vertex sequences** — the form the
Wilson-loop expansion feeds to the per-edge grouping: for each fixed
closed sequence `v`, the integrand is a positionwise product of single
matrix entries. -/
theorem trace_list_prod_eq_sum_closedSeq (l : List (Matrix ι ι R)) :
    Matrix.trace l.prod
      = ∑ v : Fin (l.length + 1) → ι,
          (if v (Fin.last l.length) = v 0 then (1 : R) else 0) *
            ∏ idx : Fin l.length,
              l.get idx (v idx.castSucc) (v idx.succ) := by
  rw [trace_list_prod_eq_sum_pathSum]
  rw [Finset.sum_congr rfl fun i _ => by rw [pathSum_eq_sum_vertexSeq]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (v 0)]
  · rw [if_pos rfl, one_mul]
  · intro i _ hi
    rw [if_neg fun h => hi h.symm, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (v 0)) h

/-! ## The map-composed form (no `List.length_map` casts)

For a Wilson loop the matrix list is `es.map f` — the edge list mapped
through the holonomy assignment.  Stating the expansion directly over
`es` and `f` keeps every binder type at `es.length` and avoids the
propositional `List.length_map` casts that the composed form
`(es.map f).length` would force on consumers. -/

/-- **Closed path expansion, map-composed form.** -/
theorem pathSum_map_eq_sum_vertexSeq {α : Type*} (es : List α)
    (f : α → Matrix ι ι R) (i j : ι) :
    pathSum (es.map f) i j
      = ∑ v : Fin (es.length + 1) → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last es.length) = j then (1 : R) else 0) *
              ∏ idx : Fin es.length,
                f (es.get idx) (v idx.castSucc) (v idx.succ) := by
  induction es generalizing i with
  | nil =>
      rw [List.map_nil, pathSum_nil]
      show _ = ∑ v : Fin 1 → ι,
        (if v 0 = i then (1 : R) else 0) *
          (if v (Fin.last 0) = j then (1 : R) else 0) *
            ∏ idx : Fin 0,
              f (([] : List α).get idx) (v idx.castSucc) (v idx.succ)
      have htrans : (∑ v : Fin 1 → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last 0) = j then (1 : R) else 0) *
              ∏ idx : Fin 0,
                f (([] : List α).get idx) (v idx.castSucc) (v idx.succ))
          = ∑ a : ι, (if a = i then (1 : R) else 0) *
              (if a = j then (1 : R) else 0) := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun v => ?_
        show (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last 0) = j then (1 : R) else 0) *
              ∏ idx : Fin 0, _ = _
        rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        rfl
      rw [htrans, Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
      · intro a _ ha
        rw [if_neg ha, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
  | cons a es ih =>
      rw [List.map_cons, pathSum_cons]
      show _ = ∑ v : Fin (es.length + 1 + 1) → ι,
        (if v 0 = i then (1 : R) else 0) *
          (if v (Fin.last (es.length + 1)) = j then (1 : R) else 0) *
            ∏ idx : Fin (es.length + 1),
              f ((a :: es).get idx) (v idx.castSucc) (v idx.succ)
      have htrans : (∑ v : Fin (es.length + 1 + 1) → ι,
          (if v 0 = i then (1 : R) else 0) *
            (if v (Fin.last (es.length + 1)) = j then (1 : R) else 0) *
              ∏ idx : Fin (es.length + 1),
                f ((a :: es).get idx) (v idx.castSucc) (v idx.succ))
          = ∑ p : ι × (Fin (es.length + 1) → ι),
              (if p.1 = i then (1 : R) else 0) *
                (if p.2 (Fin.last es.length) = j then (1 : R) else 0) *
                  (f a p.1 (p.2 0) *
                    ∏ idx : Fin es.length,
                      f (es.get idx) (p.2 idx.castSucc) (p.2 idx.succ)) := by
        refine (Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _
          fun p => ?_).symm
        simp only [Fin.consEquiv_apply]
        have hv0 : Fin.cons (α := fun _ => ι) p.1 p.2 0 = p.1 :=
          Fin.cons_zero _ _
        have hvlast : Fin.cons (α := fun _ => ι) p.1 p.2
            (Fin.last (es.length + 1)) = p.2 (Fin.last es.length) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have hprod : (∏ idx : Fin (es.length + 1),
            f ((a :: es).get idx)
              (Fin.cons (α := fun _ => ι) p.1 p.2 idx.castSucc)
              (Fin.cons (α := fun _ => ι) p.1 p.2 idx.succ))
            = f a p.1 (p.2 0) *
                ∏ idx : Fin es.length,
                  f (es.get idx) (p.2 idx.castSucc) (p.2 idx.succ) := by
          rw [Fin.prod_univ_succ]
          congr 1
        simp only [hv0, hvlast, hprod]
      rw [htrans]
      have hL : (∑ k, f a i k * pathSum (es.map f) k j)
          = ∑ w : Fin (es.length + 1) → ι,
              (if w (Fin.last es.length) = j then (1 : R) else 0) *
                (f a i (w 0) * ∏ idx : Fin es.length,
                  f (es.get idx) (w idx.castSucc) (w idx.succ)) := by
        rw [Finset.sum_congr rfl fun k _ => by
          rw [ih k, Finset.mul_sum]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_eq_single (w 0)]
        · rw [if_pos rfl, one_mul]
          ring
        · intro k _ hk
          rw [if_neg fun h => hk h.symm, zero_mul, zero_mul, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ (w 0)) h
      have hR : (∑ p : ι × (Fin (es.length + 1) → ι),
          (if p.1 = i then (1 : R) else 0) *
            (if p.2 (Fin.last es.length) = j then (1 : R) else 0) *
              (f a p.1 (p.2 0) *
                ∏ idx : Fin es.length,
                  f (es.get idx) (p.2 idx.castSucc) (p.2 idx.succ)))
          = ∑ w : Fin (es.length + 1) → ι,
              (if w (Fin.last es.length) = j then (1 : R) else 0) *
                (f a i (w 0) * ∏ idx : Fin es.length,
                  f (es.get idx) (w idx.castSucc) (w idx.succ)) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single i]
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [if_pos rfl, one_mul]
        · intro b _ hb
          refine Finset.sum_eq_zero fun w _ => ?_
          rw [if_neg hb, zero_mul, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [hR]
      exact hL

/-- **The trace as a sum over closed vertex sequences, map-composed
form** — the Wilson-loop entry expansion: for a holonomy assignment
`f` along the edge list `es`, the trace of the ordered product is a
sum over closed vertex sequences of positionwise single-entry
factors. -/
theorem trace_prod_map_eq_sum_closedSeq {α : Type*} (es : List α)
    (f : α → Matrix ι ι R) :
    Matrix.trace ((es.map f).prod)
      = ∑ v : Fin (es.length + 1) → ι,
          (if v (Fin.last es.length) = v 0 then (1 : R) else 0) *
            ∏ idx : Fin es.length,
              f (es.get idx) (v idx.castSucc) (v idx.succ) := by
  rw [trace_list_prod_eq_sum_pathSum]
  rw [Finset.sum_congr rfl fun i _ => by rw [pathSum_map_eq_sum_vertexSeq]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (v 0)]
  · rw [if_pos rfl, one_mul]
  · intro i _ hi
    rw [if_neg fun h => hi h.symm, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (v 0)) h

end YangMills
