/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonLine
import YangMills.ClayCore.TracePathExpansion
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.SchurEntryNAlitySelection
import YangMills.L0_Lattice.ChainComplex
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

/-! ## DB-2: the multi-line kill -/

/-- **The β = 0 selection rule for PRODUCTS of Wilson-line traces:**
the product-Haar expectation of `∏ⱼ tr(W_{Lⱼ})` vanishes as soon as
one positive edge has `N_c`-unbalanced TOTAL signed traversal count
across all lines.  This is DB-2's engine: the strong-coupling
expansion terms `tr(W_C)·∏_{p∈S}(tr Hₚ or conj tr Hₚ)` are exactly
such products — a conjugated plaquette trace is the trace of the
REVERSED plaquette loop — so an expansion term survives only if its
total per-edge `N`-ality balances, which is the `ZMod N_c` chain
equation of `docs/AREA-LAW-PLAN.md` §4. -/
theorem integral_prod_trace_wilsonLine_eq_zero
    {n : ℕ} (L : Fin n → List (ConcreteEdge d N)) (e₀ : PosEdge d N)
    (hdvd : ¬ (N_c : ℤ) ∣
      ((((Finset.univ.filter fun q : (Σ j : Fin n, Fin (L j).length) =>
            posEdgeOf ((L q.1).get q.2) = e₀)).filter
              fun q => ((L q.1).get q.2).sign).card : ℤ)
        - ((((Finset.univ.filter fun q : (Σ j : Fin n, Fin (L j).length) =>
            posEdgeOf ((L q.1).get q.2) = e₀)).filter
              fun q => ¬ ((L q.1).get q.2).sign).card : ℤ)) :
    ∫ A, ∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) = 0 := by
  classical
  -- expand every trace, push the product through the sums
  have hpt : (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val)
      = fun A => ∑ V ∈ Fintype.piFinset (fun j : Fin n =>
            (Finset.univ : Finset (Fin ((L j).length + 1) → Fin N_c))),
          (∏ j : Fin n, (if V j (Fin.last (L j).length) = V j 0
              then (1 : ℂ) else 0)) *
            ∏ j : Fin n, ∏ idx : Fin (L j).length,
              (if ((L j).get idx).sign
                then (configToPos A (posEdgeOf ((L j).get idx))).val
                  (V j idx.castSucc) (V j idx.succ)
                else star ((configToPos A (posEdgeOf ((L j).get idx))).val
                  (V j idx.succ) (V j idx.castSucc))) := by
    funext A
    have h1 : ∀ j : Fin n, Matrix.trace (wilsonLine A (L j)).val
        = ∑ v : Fin ((L j).length + 1) → Fin N_c,
            (if v (Fin.last (L j).length) = v 0 then (1 : ℂ) else 0) *
              ∏ idx : Fin (L j).length,
                (if ((L j).get idx).sign
                  then (configToPos A (posEdgeOf ((L j).get idx))).val
                    (v idx.castSucc) (v idx.succ)
                  else star ((configToPos A (posEdgeOf ((L j).get idx))).val
                    (v idx.succ) (v idx.castSucc))) := by
      intro j
      have hA : posToConfig (configToPos A) = A :=
        gaugeConfigEquiv.apply_symm_apply A
      conv_lhs => rw [← hA]
      exact trace_wilsonLine_eq_sum_decorated (configToPos A) (L j)
    rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    exact Finset.prod_mul_distrib
  rw [hpt]
  -- measurability and boundedness of the decorated factors
  have hsymm : Measurable
      (gaugeConfigEquiv (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))).symm := by
    rw [measurable_iff_comap_le]
    exact le_of_eq rfl
  have hcm : ∀ e : PosEdge d N, Measurable
      (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => configToPos A e) :=
    fun e => (measurable_pi_apply e).comp hsymm
  have hFm : ∀ (j : Fin n) (v : Fin ((L j).length + 1) → Fin N_c)
      (idx : Fin (L j).length),
      Measurable (fun g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        (if ((L j).get idx).sign
          then g.val (v idx.castSucc) (v idx.succ)
          else star (g.val (v idx.succ) (v idx.castSucc)))) := by
    intro j v idx
    by_cases hs : ((L j).get idx).sign = true
    · simp only [hs, if_true]
      exact (continuous_entry N_c _ _).measurable
    · simp only [hs, if_false]
      exact ((continuous_entry N_c _ _).star).measurable
  have hFb : ∀ (j : Fin n) (v : Fin ((L j).length + 1) → Fin N_c)
      (idx : Fin (L j).length)
      (g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖(if ((L j).get idx).sign
        then g.val (v idx.castSucc) (v idx.succ)
        else star (g.val (v idx.succ) (v idx.castSucc)))‖ ≤ 1 := by
    intro j v idx g
    have hg : g.val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
    by_cases hs : ((L j).get idx).sign = true
    · rw [if_pos hs]
      exact entry_norm_bound_of_unitary hg _ _
    · rw [if_neg hs, norm_star]
      exact entry_norm_bound_of_unitary hg _ _
  -- integrability of each multi-sequence term
  have hint : ∀ V ∈ Fintype.piFinset (fun j : Fin n =>
      (Finset.univ : Finset (Fin ((L j).length + 1) → Fin N_c))),
      Integrable (fun A : GaugeConfig d N
          (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        (∏ j : Fin n, (if V j (Fin.last (L j).length) = V j 0
            then (1 : ℂ) else 0)) *
          ∏ j : Fin n, ∏ idx : Fin (L j).length,
            (if ((L j).get idx).sign
              then (configToPos A (posEdgeOf ((L j).get idx))).val
                (V j idx.castSucc) (V j idx.succ)
              else star ((configToPos A (posEdgeOf ((L j).get idx))).val
                (V j idx.succ) (V j idx.castSucc))))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
    intro V _
    refine Integrable.const_mul ?_ _
    have hm : Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        ∏ j : Fin n, ∏ idx : Fin (L j).length,
          (if ((L j).get idx).sign
            then (configToPos A (posEdgeOf ((L j).get idx))).val
              (V j idx.castSucc) (V j idx.succ)
            else star ((configToPos A (posEdgeOf ((L j).get idx))).val
              (V j idx.succ) (V j idx.castSucc)))) :=
      Finset.measurable_prod _ fun j _ =>
        Finset.measurable_prod _ fun idx _ =>
          (hFm j (V j) idx).comp (hcm (posEdgeOf ((L j).get idx)))
    have hb : ∀ A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
        ‖∏ j : Fin n, ∏ idx : Fin (L j).length,
          (if ((L j).get idx).sign
            then (configToPos A (posEdgeOf ((L j).get idx))).val
              (V j idx.castSucc) (V j idx.succ)
            else star ((configToPos A (posEdgeOf ((L j).get idx))).val
              (V j idx.succ) (V j idx.castSucc)))‖ ≤ 1 := by
      intro A
      rw [norm_prod]
      calc ∏ j : Fin n, ‖∏ idx : Fin (L j).length,
            (if ((L j).get idx).sign
              then (configToPos A (posEdgeOf ((L j).get idx))).val
                (V j idx.castSucc) (V j idx.succ)
              else star ((configToPos A (posEdgeOf ((L j).get idx))).val
                (V j idx.succ) (V j idx.castSucc)))‖
          ≤ ∏ _j : Fin n, (1 : ℝ) := by
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun j _ => ?_)
            rw [norm_prod]
            calc ∏ idx : Fin (L j).length, ‖(if ((L j).get idx).sign
                  then (configToPos A (posEdgeOf ((L j).get idx))).val
                    (V j idx.castSucc) (V j idx.succ)
                  else star ((configToPos A (posEdgeOf ((L j).get idx))).val
                    (V j idx.succ) (V j idx.castSucc)))‖
                ≤ ∏ _idx : Fin (L j).length, (1 : ℝ) :=
                  Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                    (fun idx _ => hFb j (V j) idx _)
              _ = 1 := Finset.prod_const_one
        _ = 1 := Finset.prod_const_one
    have h1 : Integrable (fun _ : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
        (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
      integrable_const 1
    have h2 := h1.bdd_mul hm.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ hb)
    simpa using h2
  rw [MeasureTheory.integral_finset_sum _ hint]
  refine Finset.sum_eq_zero fun V _ => ?_
  -- regroup the double product as a product over sigma positions
  have hsig : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ j : Fin n, ∏ idx : Fin (L j).length,
        (if ((L j).get idx).sign
          then (configToPos A (posEdgeOf ((L j).get idx))).val
            (V j idx.castSucc) (V j idx.succ)
          else star ((configToPos A (posEdgeOf ((L j).get idx))).val
            (V j idx.succ) (V j idx.castSucc))))
      = fun A => ∏ q : (Σ j : Fin n, Fin (L j).length),
          (if ((L q.1).get q.2).sign
            then (configToPos A (posEdgeOf ((L q.1).get q.2))).val
              (V q.1 q.2.castSucc) (V q.1 q.2.succ)
            else star ((configToPos A (posEdgeOf ((L q.1).get q.2))).val
              (V q.1 q.2.succ) (V q.1 q.2.castSucc))) := by
    funext A
    exact (Fintype.prod_sigma' _).symm
  -- the per-term kill at the unbalanced edge
  have hmean : ∫ g, ∏ q ∈ Finset.univ.filter
      (fun q : (Σ j : Fin n, Fin (L j).length) =>
        posEdgeOf ((L q.1).get q.2) = e₀),
      (if ((L q.1).get q.2).sign
        then g.val (V q.1 q.2.castSucc) (V q.1 q.2.succ)
        else star (g.val (V q.1 q.2.succ) (V q.1 q.2.castSucc)))
      ∂(sunHaarProb N_c) = 0 := by
    have h := sunHaarProb_decoratedEntryProduct_integral_zero N_c
      (Finset.univ.filter fun q : (Σ j : Fin n, Fin (L j).length) =>
        posEdgeOf ((L q.1).get q.2) = e₀)
      (fun q => ((L q.1).get q.2).sign)
      (fun q => if ((L q.1).get q.2).sign
        then V q.1 q.2.castSucc else V q.1 q.2.succ)
      (fun q => if ((L q.1).get q.2).sign
        then V q.1 q.2.succ else V q.1 q.2.castSucc)
      hdvd
    have heq : (fun g : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
        ∏ q ∈ Finset.univ.filter
          (fun q : (Σ j : Fin n, Fin (L j).length) =>
            posEdgeOf ((L q.1).get q.2) = e₀),
          (if ((L q.1).get q.2).sign
            then g.val (V q.1 q.2.castSucc) (V q.1 q.2.succ)
            else star (g.val (V q.1 q.2.succ) (V q.1 q.2.castSucc))))
        = fun g => ∏ q ∈ Finset.univ.filter
          (fun q : (Σ j : Fin n, Fin (L j).length) =>
            posEdgeOf ((L q.1).get q.2) = e₀),
          (if ((L q.1).get q.2).sign
            then g.val
              (if ((L q.1).get q.2).sign
                then V q.1 q.2.castSucc else V q.1 q.2.succ)
              (if ((L q.1).get q.2).sign
                then V q.1 q.2.succ else V q.1 q.2.castSucc)
            else star (g.val
              (if ((L q.1).get q.2).sign
                then V q.1 q.2.castSucc else V q.1 q.2.succ)
              (if ((L q.1).get q.2).sign
                then V q.1 q.2.succ else V q.1 q.2.castSucc))) := by
      funext g
      refine Finset.prod_congr rfl fun q _ => ?_
      by_cases hs : ((L q.1).get q.2).sign = true
      · simp only [if_pos hs]
      · simp only [if_neg hs]
    rw [heq]
    exact h
  refine (MeasureTheory.integral_const_mul _ _).trans ?_
  refine mul_eq_zero_of_right _ ?_
  rw [hsig]
  exact integral_positionProduct_eq_zero (sunHaarProb N_c)
    (fun q : (Σ j : Fin n, Fin (L j).length) =>
      posEdgeOf ((L q.1).get q.2))
    (fun q g => if ((L q.1).get q.2).sign
      then g.val (V q.1 q.2.castSucc) (V q.1 q.2.succ)
      else star (g.val (V q.1 q.2.succ) (V q.1 q.2.castSucc)))
    (fun q => (hFm q.1 (V q.1) q.2).aestronglyMeasurable) e₀ hmean

/-! ## J-3(a): the bookkeeping bridge — traversal counts are the loop chain

The kill theorems' divisibility hypotheses are stated in raw
`Finset`-card form; the area-law join consumes them chain-side.  The
bridge: the signed traversal count of a positive edge `e₀` along an
edge list `es` IS `loopChain es e₀` over `ℤ`. -/

/-- Positions of a list carrying a given value, counted: the
`Fin`-indexed filter card is `List.count`. -/
theorem card_filter_get_eq_count {α : Type*} [DecidableEq α]
    (es : List α) (a : α) :
    (Finset.univ.filter fun idx : Fin es.length => es.get idx = a).card
      = es.count a := by
  induction es with
  | nil => simp
  | cons b l ih =>
      rw [Finset.card_filter]
      show (∑ idx : Fin (l.length + 1),
        if (b :: l).get idx = a then (1 : ℕ) else 0) = (b :: l).count a
      rw [Fin.sum_univ_succ]
      have hhead : ((b :: l).get 0) = b := rfl
      have htail : ∀ idx : Fin l.length, (b :: l).get idx.succ = l.get idx :=
        fun _ => rfl
      simp only [hhead, htail]
      rw [← Finset.card_filter, ih, List.count_cons]
      by_cases h : b = a <;> simp [h] <;> try omega

/-- A concrete edge traverses the positive edge `e₀` FORWARD iff it
equals `e₀` itself. -/
theorem posEdgeOf_eq_and_sign_iff (e : ConcreteEdge d N)
    (e₀ : PosEdge d N) :
    (posEdgeOf e = e₀ ∧ e.sign = true) ↔ e = (e₀ : ConcreteEdge d N) := by
  obtain ⟨ev, hev⟩ := e₀
  constructor
  · rintro ⟨hpe, hs⟩
    have h1 : ({ e with sign := true } : ConcreteEdge d N) = ev :=
      congrArg Subtype.val hpe
    have h2 : ({ e with sign := true } : ConcreteEdge d N) = e := by
      cases e with
      | mk s dir sg =>
          cases sg
          · exact absurd hs (by simp)
          · rfl
    exact h2.symm.trans h1
  · rintro rfl
    refine ⟨Subtype.ext ?_, hev⟩
    show ({ e with sign := true } : ConcreteEdge d N) = e
    cases e with
    | mk s dir sg =>
        cases sg
        · exact absurd hev (by simp)
        · rfl

/-- A concrete edge traverses the positive edge `e₀` BACKWARD iff it
equals the sign-flip of `e₀`. -/
theorem posEdgeOf_eq_and_not_sign_iff (e : ConcreteEdge d N)
    (e₀ : PosEdge d N) :
    (posEdgeOf e = e₀ ∧ ¬ e.sign = true)
      ↔ e = { (e₀ : ConcreteEdge d N) with sign := false } := by
  obtain ⟨ev, hev⟩ := e₀
  constructor
  · rintro ⟨hpe, hs⟩
    have h1 : ({ e with sign := true } : ConcreteEdge d N) = ev :=
      congrArg Subtype.val hpe
    have hsf : e.sign = false := by
      cases hsg : e.sign
      · rfl
      · exact absurd hsg hs
    cases e with
    | mk s dir sg =>
        cases ev with
        | mk s' dir' sg' =>
            simp only [ConcreteEdge.mk.injEq] at h1 ⊢
            simp only at hsf
            exact ⟨h1.1, h1.2.1, hsf⟩
  · rintro rfl
    constructor
    · refine Subtype.ext ?_
      show ({ { ev with sign := false } with sign := true } :
        ConcreteEdge d N) = ev
      cases ev with
      | mk s dir sg =>
          cases sg
          · exact absurd hev (by simp)
          · rfl
    · simp
/-- **The bridge (J-3a):** the signed traversal count of a positive
edge along an edge list — exactly the divisibility datum of the kill
theorems — IS the `ℤ`-valued loop chain at that edge. -/
theorem signed_count_eq_loopChain (es : List (ConcreteEdge d N))
    (e₀ : PosEdge d N) :
    ((((Finset.univ.filter fun idx : Fin es.length =>
          posEdgeOf (es.get idx) = e₀)).filter
            fun idx => (es.get idx).sign).card : ℤ)
      - ((((Finset.univ.filter fun idx : Fin es.length =>
          posEdgeOf (es.get idx) = e₀)).filter
            fun idx => ¬ (es.get idx).sign).card : ℤ)
    = loopChain (R := ℤ) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        es (e₀ : ConcreteEdge d N) := by
  classical
  rw [Finset.filter_filter, Finset.filter_filter]
  have h1 : (Finset.univ.filter fun idx : Fin es.length =>
      posEdgeOf (es.get idx) = e₀ ∧ (es.get idx).sign = true)
      = Finset.univ.filter fun idx =>
          es.get idx = (e₀ : ConcreteEdge d N) :=
    Finset.filter_congr fun idx _ => by
      rw [posEdgeOf_eq_and_sign_iff]
  have h2 : (Finset.univ.filter fun idx : Fin es.length =>
      posEdgeOf (es.get idx) = e₀ ∧ ¬ (es.get idx).sign = true)
      = Finset.univ.filter fun idx =>
          es.get idx = { (e₀ : ConcreteEdge d N) with sign := false } :=
    Finset.filter_congr fun idx _ => by
      rw [posEdgeOf_eq_and_not_sign_iff]
  rw [h1, h2, card_filter_get_eq_count, card_filter_get_eq_count]
  unfold loopChain
  rw [finBoxGeometry_reverse]
  have hflip : ({ (e₀ : ConcreteEdge d N) with
      sign := !(e₀ : ConcreteEdge d N).sign } : ConcreteEdge d N)
      = { (e₀ : ConcreteEdge d N) with sign := false } := by
    rw [e₀.2]
    rfl
  rw [hflip]
  -- the two `List.count`s differ only in their (subsingleton) `Decidable`
  -- instance arguments: `loopChain` was defined under `open Classical in`
  congr!
/-- `loopChain` over `ZMod N_c` is the mod-`N_c` reduction of the
`ℤ`-valued chain. -/
theorem loopChain_zmod_eq_intCast (es : List (ConcreteEdge d N))
    (e : ConcreteEdge d N) :
    loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es e
      = ((loopChain (R := ℤ) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es e : ℤ) :
            ZMod N_c) := by
  unfold loopChain
  push_cast
  ring

/-- **The chain-side selection rule (J-3, single loop):** the β = 0
Haar expectation of a Wilson-loop trace vanishes unless the loop's
`1`-chain vanishes mod `N_c` at every (positive) edge — the statement
the area-law spanning argument consumes. -/
theorem integral_trace_wilsonLine_eq_zero_of_loopChain_ne_zero
    (es : List (ConcreteEdge d N)) (e₀ : PosEdge d N)
    (h : loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        es (e₀ : ConcreteEdge d N) ≠ 0) :
    ∫ A, Matrix.trace (wilsonLine A es).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) = 0 := by
  refine integral_trace_wilsonLine_eq_zero es e₀ fun hdvd => h ?_
  rw [loopChain_zmod_eq_intCast, ← signed_count_eq_loopChain es e₀]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd

end YangMills
