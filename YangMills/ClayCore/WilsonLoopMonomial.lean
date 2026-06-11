/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonLine
import YangMills.ClayCore.TracePathExpansion
import YangMills.L1_GibbsMeasure.GibbsMeasure

/-!
# The Wilson loop as a sum of decorated entry monomials (AL4.5, J-1)

`docs/AREA-LAW-PLAN.md` §4: the SU(N_c)-specific wiring of the join.
Three steps, all banked after this file:

* `sun_inv_val_apply` — unitarity at the entry level: the inverse's
  entries are the conjugated transposed entries (a backward edge
  traversal contributes ANTIholomorphic factors);
* `wilsonLine_val` — the subtype-to-matrix bridge: the matrix of a
  Wilson line is the ordered product of the edge holonomy matrices;
* `trace_wilsonLine_eq_sum_decorated` — the master expansion: the
  Wilson-loop trace is a sum over closed vertex sequences of
  positionwise DECORATED entries of the positive-edge coordinates —
  entry if the edge is traversed forward, conjugated entry if
  backward.  For fixed `v` this is exactly the input shape of the
  per-edge grouping `prod_comp_eq_prod_fiber` with the decorated
  selection rule `sunHaarProb_decoratedEntryProduct_integral_zero`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open GaugeConfig

variable {d N N_c : ℕ} [NeZero d] [NeZero N] [NeZero N_c]

omit [NeZero N_c] in
/-- **Unitarity at the entry level:** on `SU(N_c)` the inverse's
entries are the conjugated transposed entries. -/
theorem sun_inv_val_apply
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (a b : Fin N_c) :
    (U⁻¹).val a b = star (U.val b a) := by
  show (star U).val a b = _
  rw [Matrix.specialUnitaryGroup.coe_star, Matrix.star_apply]

/-- The **positive representative** of a concrete edge: forget the
sign.  The Haar coordinate an edge traversal reads. -/
def posEdgeOf (e : ConcreteEdge d N) : PosEdge d N :=
  ⟨{ e with sign := true }, rfl⟩

omit [NeZero d] [NeZero N] in
/-- **Entry decoration of a coordinate configuration:** evaluating the
gauge field built from positive-edge coordinates `x` on any concrete
edge gives, entrywise, the coordinate's entry when the edge is
positive and the conjugated transposed entry when negative. -/
theorem posToFun_val_apply
    (x : PosEdge d N → ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    (e : ConcreteEdge d N) (a b : Fin N_c) :
    (posToFun x e).val a b
      = if e.sign
          then (x (posEdgeOf e)).val a b
          else star ((x (posEdgeOf e)).val b a) := by
  unfold posToFun posEdgeOf
  by_cases h : e.sign = true
  · rw [dif_pos h, if_pos h]
    have he : (⟨e, h⟩ : PosEdge d N) = ⟨{ e with sign := true }, rfl⟩ := by
      refine Subtype.ext ?_
      cases e with
      | mk s dir sg =>
          cases sg
          · exact absurd h (by simp)
          · rfl
    rw [he]
  · rw [dif_neg h, if_neg h, sun_inv_val_apply]

omit [NeZero N_c] in
/-- **The matrix of a Wilson line** is the ordered product of the edge
holonomy matrices — the `Submonoid` coercion commutes with the list
product. -/
theorem wilsonLine_val
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) :
    (wilsonLine A es).val = (es.map fun e => (A e).val).prod := by
  unfold wilsonLine
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  rfl

/-- **The master decorated expansion (J-1):** the Wilson-loop trace in
positive-edge coordinates is a sum over closed vertex sequences of
positionwise decorated entries — `U_{ab}` for forward traversals,
`conj U_{ba}` for backward ones.  Per fixed sequence `v`, this is the
positionwise edge-product shape that `prod_comp_eq_prod_fiber` groups
and `sunHaarProb_decoratedEntryProduct_integral_zero` kills at any
`N`-ality-unbalanced edge. -/
theorem trace_wilsonLine_eq_sum_decorated
    (x : PosEdge d N → ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    (es : List (ConcreteEdge d N)) :
    Matrix.trace (wilsonLine (posToConfig x) es).val
      = ∑ v : Fin (es.length + 1) → Fin N_c,
          (if v (Fin.last es.length) = v 0 then (1 : ℂ) else 0) *
            ∏ idx : Fin es.length,
              (if (es.get idx).sign
                then (x (posEdgeOf (es.get idx))).val
                  (v idx.castSucc) (v idx.succ)
                else star ((x (posEdgeOf (es.get idx))).val
                  (v idx.succ) (v idx.castSucc))) := by
  rw [wilsonLine_val, trace_prod_map_eq_sum_closedSeq]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun idx _ => ?_
  show (posToFun x (es.get idx)).val (v idx.castSucc) (v idx.succ) = _
  rw [posToFun_val_apply]

end YangMills
