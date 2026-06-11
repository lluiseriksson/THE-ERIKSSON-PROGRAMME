/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonLine
import YangMills.ClayCore.TracePathExpansion
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.SchurEntryNAlitySelection
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

open MeasureTheory GaugeConfig

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

/-! ## J-2: the pure-loop kill -/

/-- **The `N`-ality selection rule for Wilson loops at β = 0:** the
product-Haar expectation of a Wilson-loop trace vanishes as soon as
ONE positive edge has `N_c`-unbalanced signed traversal count
(forward count minus backward count not divisible by `N_c`).  In
particular every open line and every loop traversing some edge
exactly once has zero Haar expectation.  Pipeline: the decorated
expansion (`trace_wilsonLine_eq_sum_decorated`) + the per-edge
grouping/kill (`integral_positionProduct_eq_zero`) + the decorated
selection rule (`sunHaarProb_decoratedEntryProduct_integral_zero`). -/
theorem integral_trace_wilsonLine_eq_zero
    (es : List (ConcreteEdge d N)) (e₀ : PosEdge d N)
    (hdvd : ¬ (N_c : ℤ) ∣
      ((((Finset.univ.filter fun idx : Fin es.length =>
            posEdgeOf (es.get idx) = e₀)).filter
              fun idx => (es.get idx).sign).card : ℤ)
        - ((((Finset.univ.filter fun idx : Fin es.length =>
            posEdgeOf (es.get idx) = e₀)).filter
              fun idx => ¬ (es.get idx).sign).card : ℤ)) :
    ∫ A, Matrix.trace (wilsonLine A es).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) = 0 := by
  classical
  -- expand the integrand into decorated closed-path terms
  have hpt : (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val)
      = fun A => ∑ v : Fin (es.length + 1) → Fin N_c,
          (if v (Fin.last es.length) = v 0 then (1 : ℂ) else 0) *
            ∏ idx : Fin es.length,
              (if (es.get idx).sign
                then (configToPos A (posEdgeOf (es.get idx))).val
                  (v idx.castSucc) (v idx.succ)
                else star ((configToPos A (posEdgeOf (es.get idx))).val
                  (v idx.succ) (v idx.castSucc))) := by
    funext A
    have hA : posToConfig (configToPos A) = A :=
      gaugeConfigEquiv.apply_symm_apply A
    conv_lhs => rw [← hA]
    exact trace_wilsonLine_eq_sum_decorated (configToPos A) es
  rw [hpt]
  -- measurability of the pieces
  have hsymm : Measurable
      (gaugeConfigEquiv (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))).symm := by
    rw [measurable_iff_comap_le]
    exact le_of_eq rfl
  have hcm : ∀ e : PosEdge d N, Measurable
      (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => configToPos A e) :=
    fun e => (measurable_pi_apply e).comp hsymm
  have hFm : ∀ (v : Fin (es.length + 1) → Fin N_c) (idx : Fin es.length),
      Measurable (fun g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        (if (es.get idx).sign
          then g.val (v idx.castSucc) (v idx.succ)
          else star (g.val (v idx.succ) (v idx.castSucc)))) := by
    intro v idx
    by_cases hs : (es.get idx).sign = true
    · simp only [hs, if_true]
      exact (continuous_entry N_c _ _).measurable
    · simp only [hs, if_false]
      exact ((continuous_entry N_c _ _).star).measurable
  -- boundedness of the decorated factors
  have hFb : ∀ (v : Fin (es.length + 1) → Fin N_c) (idx : Fin es.length)
      (g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖(if (es.get idx).sign
        then g.val (v idx.castSucc) (v idx.succ)
        else star (g.val (v idx.succ) (v idx.castSucc)))‖ ≤ 1 := by
    intro v idx g
    have hg : g.val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
    by_cases hs : (es.get idx).sign = true
    · rw [if_pos hs]
      exact entry_norm_bound_of_unitary hg _ _
    · rw [if_neg hs, norm_star]
      exact entry_norm_bound_of_unitary hg _ _
  -- integrability of each closed-path term
  have hint : ∀ v ∈ (Finset.univ : Finset (Fin (es.length + 1) → Fin N_c)),
      Integrable (fun A : GaugeConfig d N
          (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        (if v (Fin.last es.length) = v 0 then (1 : ℂ) else 0) *
          ∏ idx : Fin es.length,
            (if (es.get idx).sign
              then (configToPos A (posEdgeOf (es.get idx))).val
                (v idx.castSucc) (v idx.succ)
              else star ((configToPos A (posEdgeOf (es.get idx))).val
                (v idx.succ) (v idx.castSucc))))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
    intro v _
    refine Integrable.const_mul ?_ _
    have hm : Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        ∏ idx : Fin es.length,
          (if (es.get idx).sign
            then (configToPos A (posEdgeOf (es.get idx))).val
              (v idx.castSucc) (v idx.succ)
            else star ((configToPos A (posEdgeOf (es.get idx))).val
              (v idx.succ) (v idx.castSucc)))) :=
      Finset.measurable_prod _ fun idx _ =>
        (hFm v idx).comp (hcm (posEdgeOf (es.get idx)))
    have hb : ∀ A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
        ‖∏ idx : Fin es.length,
          (if (es.get idx).sign
            then (configToPos A (posEdgeOf (es.get idx))).val
              (v idx.castSucc) (v idx.succ)
            else star ((configToPos A (posEdgeOf (es.get idx))).val
              (v idx.succ) (v idx.castSucc)))‖ ≤ 1 := by
      intro A
      rw [norm_prod]
      calc ∏ idx : Fin es.length, ‖(if (es.get idx).sign
            then (configToPos A (posEdgeOf (es.get idx))).val
              (v idx.castSucc) (v idx.succ)
            else star ((configToPos A (posEdgeOf (es.get idx))).val
              (v idx.succ) (v idx.castSucc)))‖
          ≤ ∏ _idx : Fin es.length, (1 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun idx _ => hFb v idx _)
        _ = 1 := Finset.prod_const_one
    have h1 : Integrable (fun _ : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
      integrable_const 1
    have h2 := h1.bdd_mul hm.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ hb)
    simpa using h2
  rw [MeasureTheory.integral_finset_sum _ hint]
  refine Finset.sum_eq_zero fun v _ => ?_
  -- the per-term kill at the unbalanced edge
  have hmean : ∫ g, ∏ idx ∈ Finset.univ.filter
      (fun idx : Fin es.length => posEdgeOf (es.get idx) = e₀),
      (if (es.get idx).sign
        then g.val (v idx.castSucc) (v idx.succ)
        else star (g.val (v idx.succ) (v idx.castSucc)))
      ∂(sunHaarProb N_c) = 0 := by
    have h := sunHaarProb_decoratedEntryProduct_integral_zero N_c
      (Finset.univ.filter fun idx : Fin es.length =>
        posEdgeOf (es.get idx) = e₀)
      (fun idx => (es.get idx).sign)
      (fun idx => if (es.get idx).sign then v idx.castSucc else v idx.succ)
      (fun idx => if (es.get idx).sign then v idx.succ else v idx.castSucc)
      hdvd
    have heq : (fun g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        ∏ idx ∈ Finset.univ.filter
          (fun idx : Fin es.length => posEdgeOf (es.get idx) = e₀),
          (if (es.get idx).sign
            then g.val (v idx.castSucc) (v idx.succ)
            else star (g.val (v idx.succ) (v idx.castSucc))))
        = fun g => ∏ idx ∈ Finset.univ.filter
          (fun idx : Fin es.length => posEdgeOf (es.get idx) = e₀),
          (if (es.get idx).sign
            then g.val
              (if (es.get idx).sign then v idx.castSucc else v idx.succ)
              (if (es.get idx).sign then v idx.succ else v idx.castSucc)
            else star (g.val
              (if (es.get idx).sign then v idx.castSucc else v idx.succ)
              (if (es.get idx).sign then v idx.succ else v idx.castSucc))) := by
      funext g
      refine Finset.prod_congr rfl fun idx _ => ?_
      by_cases hs : (es.get idx).sign = true
      · simp only [if_pos hs]
      · simp only [if_neg hs]
    rw [heq]
    exact h
  refine (MeasureTheory.integral_const_mul _ _).trans ?_
  exact mul_eq_zero_of_right _
    (integral_positionProduct_eq_zero (sunHaarProb N_c)
      (fun idx => posEdgeOf (es.get idx))
      (fun idx g => if (es.get idx).sign
        then g.val (v idx.castSucc) (v idx.succ)
        else star (g.val (v idx.succ) (v idx.castSucc)))
      (fun idx => (hFm v idx).aestronglyMeasurable) e₀ hmean)

end YangMills
