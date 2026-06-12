/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonLine
import YangMills.ClayCore.TracePathExpansion
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.SchurEntryNAlitySelection
import YangMills.L0_Lattice.ChainComplex
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L1_GibbsMeasure.WilsonLoopExpansion
import YangMills.L1_GibbsMeasure.ExpActivityExpansion

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

/-! ## J-3(b): the multi-line bridge and chain-side rule -/

/-- Filters over sigma position types decompose linewise. -/
theorem card_filter_sigma_eq_sum {n : ℕ} {κ : Fin n → Type*}
    [∀ j, Fintype (κ j)] (Q : (Σ j : Fin n, κ j) → Prop)
    [DecidablePred Q] :
    (Finset.univ.filter Q).card
      = ∑ j : Fin n, (Finset.univ.filter fun y : κ j => Q ⟨j, y⟩).card := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => by rw [← Finset.card_filter]

/-- **The multi-line bridge (J-3b):** the total signed traversal count
of `e₀` across a family of lines — the divisibility datum of the
multi-line kill — is the SUM of the lines' loop chains at `e₀`. -/
theorem sigma_signed_count_eq_sum_loopChain {n : ℕ}
    (L : Fin n → List (ConcreteEdge d N)) (e₀ : PosEdge d N) :
    ((((Finset.univ.filter fun q : (Σ j : Fin n, Fin (L j).length) =>
          posEdgeOf ((L q.1).get q.2) = e₀)).filter
            fun q => ((L q.1).get q.2).sign).card : ℤ)
      - ((((Finset.univ.filter fun q : (Σ j : Fin n, Fin (L j).length) =>
          posEdgeOf ((L q.1).get q.2) = e₀)).filter
            fun q => ¬ ((L q.1).get q.2).sign).card : ℤ)
    = ∑ j : Fin n, loopChain (R := ℤ) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (L j) (e₀ : ConcreteEdge d N) := by
  classical
  rw [Finset.filter_filter, Finset.filter_filter]
  rw [card_filter_sigma_eq_sum
        (fun q : (Σ j : Fin n, Fin (L j).length) =>
          posEdgeOf ((L q.1).get q.2) = e₀ ∧ ((L q.1).get q.2).sign = true),
      card_filter_sigma_eq_sum
        (fun q : (Σ j : Fin n, Fin (L j).length) =>
          posEdgeOf ((L q.1).get q.2) = e₀ ∧
            ¬ ((L q.1).get q.2).sign = true)]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((Finset.univ.filter fun idx : Fin (L j).length =>
      posEdgeOf ((L j).get idx) = e₀ ∧ ((L j).get idx).sign = true).card : ℤ)
    - ((Finset.univ.filter fun idx : Fin (L j).length =>
      posEdgeOf ((L j).get idx) = e₀ ∧
        ¬ ((L j).get idx).sign = true).card : ℤ)
    = _
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact signed_count_eq_loopChain (L j) e₀

/-- **The multi-line chain-side selection rule (J-3b):** a product of
Wilson-line traces has zero β = 0 Haar expectation unless the SUM of
the lines' loop chains vanishes mod `N_c` at every positive edge.
For the strong-coupling family `loop C :: (plaquette or reversed
plaquette loops of S)` this hypothesis at `e₀` IS the failure of the
chain equation `loopChain C + ∂₂σ = 0` there — the area-law join's
final analytic input. -/
theorem integral_prod_trace_wilsonLine_eq_zero_of_sum_loopChain_ne_zero
    {n : ℕ} (L : Fin n → List (ConcreteEdge d N)) (e₀ : PosEdge d N)
    (h : (∑ j : Fin n, loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (L j) (e₀ : ConcreteEdge d N)) ≠ 0) :
    ∫ A, ∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) = 0 := by
  refine integral_prod_trace_wilsonLine_eq_zero L e₀ fun hdvd => h ?_
  have hcast : (∑ j : Fin n, loopChain (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (L j) (e₀ : ConcreteEdge d N))
      = (((∑ j : Fin n, loopChain (R := ℤ) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (L j) (e₀ : ConcreteEdge d N)) : ℤ) : ZMod N_c) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun j _ => loopChain_zmod_eq_intCast (L j) _
  rw [hcast, ← sigma_signed_count_eq_sum_loopChain L e₀]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd

/-! ## The join (ii-final): surviving terms span — `T ≠ 0 ⇒ Area ≤ m` -/

open Classical in
/-- **THE AREA-LAW JOIN (sharp form):** if a strong-coupling expansion
term — the Wilson loop times `m` σ-signed plaquette traces (conjugate
choice = reversed list) — has NONZERO β = 0 Haar expectation, then the
loop's `N`-ality area is at most the number of DISTINCT plaquettes
used (multiplicity-sharp: the input of the exact-activity campaign's
E3).  Pipeline: contraposition of the multi-line chain-side selection
rule ⇒ the total chain vanishes at every positive edge ⇒
(orientation-oddness) everywhere ⇒ the antisymmetrized chain equation
`∂₂A σ' = −loopChain C` with `supp σ' ⊆ image ps` ⇒
`chainAreaA_le_card_of_support_subset` + `chainAreaA_neg`. -/
theorem chainAreaA_loopChain_le_card_image_of_integral_ne_zero
    {m : ℕ} (es : List (ConcreteEdge d N))
    (ps : Fin m → FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (σ : Fin m → Bool)
    (hT : ∫ A, ∏ j : Fin (m + 1),
        Matrix.trace (wilsonLine A
          (Fin.cons (α := fun _ => List (ConcreteEdge d N)) es (fun i =>
            if σ i
            then plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
            else ((plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                (FiniteLatticeGeometry.reverse (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
            j)).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) ≠ 0) :
    chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
      ≤ (Finset.univ.image ps).card := by
  classical
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  set L : Fin (m + 1) → List (ConcreteEdge d N) :=
    Fin.cons (α := fun _ => List (ConcreteEdge d N)) es (fun i =>
    if σ i
    then plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
    else ((plaquetteList (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
        (FiniteLatticeGeometry.reverse (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
    with hL
  set τ : Fin m → ZMod N_c := fun i => if σ i then 1 else -1 with hτ
  set σ' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ZMod N_c :=
    fun p => ∑ i ∈ Finset.univ.filter (fun i => ps i = p), τ i with hσ'
  -- contraposition of the chain-side selection rule
  have hsum : ∀ e₀ : PosEdge d N,
      (∑ j : Fin (m + 1), loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (L j) (e₀ : ConcreteEdge d N)) = 0 := by
    intro e₀
    by_contra hne
    exact hT
      (integral_prod_trace_wilsonLine_eq_zero_of_sum_loopChain_ne_zero
        L e₀ hne)
  -- the total chain is orientation-odd, so it vanishes everywhere
  have hodd : ∀ e : ConcreteEdge d N,
      (∑ j : Fin (m + 1), loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (L j)
        (FiniteLatticeGeometry.reverse (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) e))
      = - ∑ j : Fin (m + 1), loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (L j) e := by
    intro e
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ =>
      loopChain_reverse (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (L j) e
  have hTc : ∀ e : ConcreteEdge d N,
      (∑ j : Fin (m + 1), loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (L j) e) = 0 := by
    intro e
    by_cases hs : e.sign = true
    · exact hsum ⟨e, hs⟩
    · have hrs : (FiniteLatticeGeometry.reverse (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) e).sign = true := by
        rw [finBoxGeometry_reverse]
        cases hsb : e.sign
        · rfl
        · exact absurd hsb hs
      have h0 := hsum ⟨FiniteLatticeGeometry.reverse (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) e, hrs⟩
      have h1 := hodd e
      rw [h0] at h1
      exact neg_eq_zero.mp h1.symm
  -- identify the total chain with the antisymmetrized chain equation
  have hchain : ∀ e : ConcreteEdge d N,
      loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es e
      + chainBoundary₂A (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) σ' e = 0 := by
    intro e
    have h1 := hTc e
    rw [Fin.sum_univ_succ] at h1
    simp only [hL, Fin.cons_zero, Fin.cons_succ] at h1
    have h2 : ∀ i : Fin m,
        loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (if σ i
            then plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
            else ((plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                (FiniteLatticeGeometry.reverse (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
          e
        = τ i * loopChain (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)) e := by
      intro i
      by_cases hsi : σ i = true
      · rw [if_pos hsi]
        simp only [hτ, if_pos hsi, one_mul]
      · rw [if_neg hsi, loopChain_reverse_list]
        simp only [hτ, if_neg hsi]
        ring
    rw [Finset.sum_congr rfl fun i _ => h2 i] at h1
    have h3 : (∑ p : FiniteLatticeGeometry.P (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
        σ' p * loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p) e)
        = ∑ i : Fin m, τ i * loopChain (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)) e := by
      rw [Finset.sum_congr rfl fun p _ => by
        rw [hσ', Finset.sum_mul]]
      rw [← Finset.sum_fiberwise_of_maps_to (g := ps)
        (fun i _ => Finset.mem_univ (ps i))
        (fun i => τ i * loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)) e)]
      refine Finset.sum_congr rfl fun p _ =>
        Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    rw [← h3] at h1
    rw [show (∑ p : FiniteLatticeGeometry.P (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
        σ' p * loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p) e)
        = chainBoundary₂A (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) σ' e from
      sum_mul_loopChain_plaquette_list_eq_chainBoundary₂A σ' e] at h1
    exact h1
  -- the chain equation and the support bound
  have heq : chainBoundary₂A (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) σ'
      = fun e => - loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es e := by
    funext e
    exact eq_neg_of_add_eq_zero_right (hchain e)
  have hsupp : chainSupport (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) σ'
      ⊆ Finset.univ.image ps := by
    intro p hp
    simp only [chainSupport, Finset.mem_filter] at hp
    have hne : σ' p ≠ 0 := hp.2
    by_contra hnotin
    apply hne
    have hempty : Finset.univ.filter (fun i => ps i = p) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun {i} _ hpi =>
        hnotin (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hpi⟩)
    simp only [hσ', hempty, Finset.sum_empty]
  have hbound := chainAreaA_le_card_of_support_subset (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) heq hsupp
  rw [chainAreaA_neg] at hbound
  exact hbound

/-- **THE AREA-LAW JOIN** (multiplicity-blind form): surviving terms
bound the area by the number of LINES.  Derived from the sharper
image-card form; kept as the interface AL6-1 consumes. -/
theorem chainAreaA_loopChain_le_of_integral_ne_zero
    {m : ℕ} (es : List (ConcreteEdge d N))
    (ps : Fin m → FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (σ : Fin m → Bool)
    (hT : ∫ A, ∏ j : Fin (m + 1),
        Matrix.trace (wilsonLine A
          (Fin.cons (α := fun _ => List (ConcreteEdge d N)) es (fun i =>
            if σ i
            then plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
            else ((plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                (FiniteLatticeGeometry.reverse (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
            j)).val
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) ≠ 0) :
    chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es) ≤ m := by
  classical
  refine le_trans
    (chainAreaA_loopChain_le_card_image_of_integral_ne_zero es ps σ hT)
    (le_trans Finset.card_image_le ?_)
  simp

/-! ## AL6 enablers: bounds, measurability, integrability -/

/-- Wilson-line traces are **bounded by `N_c`** — the trace of a
unitary matrix is a sum of `N_c` entries of norm `≤ 1`. -/
theorem norm_trace_wilsonLine_le
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (ConcreteEdge d N)) :
    ‖Matrix.trace (wilsonLine A es).val‖ ≤ (N_c : ℝ) := by
  have hU : (wilsonLine A es).val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp (wilsonLine A es).property).1
  have heq : Matrix.trace (wilsonLine A es).val
      = ∑ i : Fin N_c, (wilsonLine A es).val i i := by
    simp [Matrix.trace, Matrix.diag]
  rw [heq]
  calc ‖∑ i : Fin N_c, (wilsonLine A es).val i i‖
      ≤ ∑ i : Fin N_c, ‖(wilsonLine A es).val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N_c, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hU i i
    _ = (N_c : ℝ) := by simp

/-- The decorated expansion at an **arbitrary** configuration —
`J-2`'s integrand rewrite as a standalone lemma. -/
theorem trace_wilsonLine_eq_sum_decorated_config
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (ConcreteEdge d N)) :
    Matrix.trace (wilsonLine A es).val
      = ∑ v : Fin (es.length + 1) → Fin N_c,
          (if v (Fin.last es.length) = v 0 then (1 : ℂ) else 0) *
            ∏ idx : Fin es.length,
              (if (es.get idx).sign
                then (configToPos A (posEdgeOf (es.get idx))).val
                  (v idx.castSucc) (v idx.succ)
                else star ((configToPos A (posEdgeOf (es.get idx))).val
                  (v idx.succ) (v idx.castSucc))) := by
  have hA : posToConfig (configToPos A) = A :=
    gaugeConfigEquiv.apply_symm_apply A
  conv_lhs => rw [← hA]
  exact trace_wilsonLine_eq_sum_decorated (configToPos A) es

/-- Wilson-line traces are **measurable** in the configuration —
via the decorated expansion (a finite sum of products of measurable
coordinate entries), avoiding group-operation measurability
entirely. -/
theorem measurable_trace_wilsonLine (es : List (ConcreteEdge d N)) :
    Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val) := by
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
                  (v idx.succ) (v idx.castSucc))) :=
    funext fun A => trace_wilsonLine_eq_sum_decorated_config A es
  rw [hpt]
  have hsymm : Measurable
      (gaugeConfigEquiv (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))).symm := by
    rw [measurable_iff_comap_le]
    exact le_of_eq rfl
  have hcm : ∀ e : PosEdge d N, Measurable
      (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => configToPos A e) :=
    fun e => (measurable_pi_apply e).comp hsymm
  refine Finset.measurable_sum _ fun v _ => ?_
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_prod _ fun idx _ => ?_
  by_cases hs : (es.get idx).sign = true
  · simp only [hs, if_true]
    exact ((continuous_entry N_c _ _).measurable).comp
      (hcm (posEdgeOf (es.get idx)))
  · simp only [hs, if_false]
    exact (((continuous_entry N_c _ _).star).measurable).comp
      (hcm (posEdgeOf (es.get idx)))

/-- Products of Wilson-line traces are **integrable** under the gauge
measure, being measurable and bounded by `N_c^n` — the integrability
input for every AL6 expansion/swap step. -/
theorem integrable_prod_trace_wilsonLine {n : ℕ}
    (L : Fin n → List (ConcreteEdge d N)) :
    Integrable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val)
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      ∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val) :=
    Finset.measurable_prod _ fun j _ => measurable_trace_wilsonLine (L j)
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖∏ j : Fin n, Matrix.trace (wilsonLine A (L j)).val‖
        ≤ (N_c : ℝ) ^ n := by
    intro A
    rw [norm_prod]
    calc ∏ j : Fin n, ‖Matrix.trace (wilsonLine A (L j)).val‖
        ≤ ∏ _j : Fin n, (N_c : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun j _ => norm_trace_wilsonLine_le A (L j))
      _ = (N_c : ℝ) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : Integrable (fun _ : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
    integrable_const 1
  have h2 := h1.bdd_mul hm.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ hb)
  simpa using h2

/-- **The conjugated trace is the reversed-line trace** — the last
semantic bridge of the area-law expansion: the antiholomorphic
activity choice `conj tr(Hₚ)` IS the Wilson trace of the reversed
plaquette list, so every σ-term of the strong-coupling expansion is a
product of Wilson-line traces, as the join requires. -/
theorem star_trace_wilsonLine
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (ConcreteEdge d N)) :
    Matrix.trace (wilsonLine A
        ((es.map (FiniteLatticeGeometry.reverse (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)).val
      = star (Matrix.trace (wilsonLine A es).val) := by
  rw [wilsonLine_reverse_list]
  calc Matrix.trace ((wilsonLine A es)⁻¹).val
      = Matrix.trace (star ((wilsonLine A es).val)) := rfl
    _ = star (Matrix.trace (wilsonLine A es).val) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]

open Classical in
/-- The **power-trace observable**: the Wilson loop times
plaquette-trace powers — the generic term of the exp-expanded Wilson
Boltzmann factor. -/
noncomputable def powerTraceObservable (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ)
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))) :
    ℂ :=
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  Matrix.trace (wilsonLine A es).val *
    ∏ p, (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val ^ (j p) *
      star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) ^ (k p))

open Classical in
/-- **The multiplicity join (exact-activity E3b):** if the Wilson loop
times plaquette-trace POWERS `∏_p tr(Hₚ)^{jₚ}·(conj tr Hₚ)^{kₚ}` has
nonzero β = 0 expectation, the loop's `N`-ality area is bounded by
the number of plaquettes actually used — `#{p : jₚ + kₚ ≠ 0}`.
Powers become repeated lines over `Σ p, Fin (jₚ) ⊕ Fin (kₚ)`, and the
SHARP join counts distinct plaquettes only. -/
theorem chainAreaA_le_card_support_of_integral_pow_ne_zero
    (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ)
    (hT : ∫ A, powerTraceObservable es j k A
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) ≠ 0) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
      ≤ (Finset.univ.filter (fun p => j p + k p ≠ 0)).card := by
  classical
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  set κ := (Σ p : FiniteLatticeGeometry.P (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
    (Fin (j p) ⊕ Fin (k p))) with hκ
  set eκ := Fintype.equivFin κ with heκ
  set ps : Fin (Fintype.card κ) → FiniteLatticeGeometry.P (d := d)
      (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :=
    fun i => (eκ.symm i).1 with hps
  set σb : Fin (Fintype.card κ) → Bool :=
    fun i => ((eκ.symm i).2).isLeft with hσb
  -- the integrand in family form
  have hint : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      powerTraceObservable es j k A)
      = fun A => ∏ i : Fin (Fintype.card κ + 1),
          Matrix.trace (wilsonLine A
            (Fin.cons (α := fun _ => List (ConcreteEdge d N)) es (fun i =>
              if σb i
              then plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
              else ((plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                  (FiniteLatticeGeometry.reverse (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
              i)).val := by
    funext A
    show Matrix.trace (wilsonLine A es).val *
      ∏ p, (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val ^ (j p) *
        star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) ^ (k p))
      = _
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    -- per plaquette: powers as products over the sum type
    have hper : ∀ p : FiniteLatticeGeometry.P (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
        (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val ^ (j p) *
          star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) ^ (k p))
        = ∏ s : Fin (j p) ⊕ Fin (k p),
            (if s.isLeft
              then Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              else star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) := by
      intro p
      rw [Fintype.prod_sum_type]
      congr 1
      · refine ((Finset.prod_congr rfl fun s _ =>
          (if_pos rfl)).trans ?_).symm
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · refine ((Finset.prod_congr rfl fun s _ =>
          (if_neg Bool.false_ne_true)).trans ?_).symm
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_congr rfl fun p _ => hper p]
    rw [← Fintype.prod_sigma' (fun p (s : Fin (j p) ⊕ Fin (k p)) =>
      (if s.isLeft
        then Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        else star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))]
    -- reindex the sigma product through `eκ`
    refine (Fintype.prod_equiv eκ.symm _ _ fun i => ?_).symm
    by_cases hs : ((eκ.symm i).2).isLeft = true
    · rw [if_pos hs, if_pos (by simp [hσb, hs])]
    · rw [if_neg hs, if_neg (by simp [hσb, hs]),
        star_trace_wilsonLine]
  rw [hint] at hT
  have hsharp := chainAreaA_loopChain_le_card_image_of_integral_ne_zero
    es ps σb hT
  refine le_trans hsharp (le_of_eq ?_)
  congr 1
  -- the image of `ps` is exactly the support of the multiplicities
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨i, hi⟩
    intro hzero
    have hj : j p = 0 := by omega
    have hk : k p = 0 := by omega
    have hp' : (eκ.symm i).1 = p := hi
    have hq2 := (eκ.symm i).2
    rw [hp', hj, hk] at hq2
    exact hq2.elim (fun a => a.elim0) (fun b => b.elim0)
  · intro hne
    by_cases hj : j p ≠ 0
    · refine ⟨eκ ⟨p, Sum.inl ⟨0, Nat.pos_of_ne_zero hj⟩⟩, ?_⟩
      show (eκ.symm (eκ ⟨p, Sum.inl ⟨0, Nat.pos_of_ne_zero hj⟩⟩)).1 = p
      rw [eκ.symm_apply_apply]
    · have hk : k p ≠ 0 := by omega
      refine ⟨eκ ⟨p, Sum.inr ⟨0, Nat.pos_of_ne_zero hk⟩⟩, ?_⟩
      show (eκ.symm (eκ ⟨p, Sum.inr ⟨0, Nat.pos_of_ne_zero hk⟩⟩)).1 = p
      rw [eκ.symm_apply_apply]

open Classical in
/-- The power-trace observable is **measurable**. -/
theorem measurable_powerTraceObservable (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ) :
    Measurable (powerTraceObservable es j k) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  refine (measurable_trace_wilsonLine es).mul
    (Finset.measurable_prod _ fun p _ => Measurable.mul ?_ ?_)
  · exact (measurable_trace_wilsonLine _).pow_const _
  · exact ((continuous_star.measurable).comp
      (measurable_trace_wilsonLine _)).pow_const _

open Classical in
/-- The power-trace observable is **pointwise bounded by
`N_c^(1 + Σ(jₚ + kₚ))`**. -/
theorem norm_powerTraceObservable_le
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖powerTraceObservable es j k A‖
      ≤ (N_c : ℝ) ^ (1 + ∑ p, (j p + k p)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have hN0 : (0 : ℝ) ≤ (N_c : ℝ) := Nat.cast_nonneg _
  show ‖Matrix.trace (wilsonLine A es).val * ∏ p, _‖ ≤ _
  rw [norm_mul, norm_prod, pow_add, pow_one]
  refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_ ?_ hN0
  · calc (∏ p, ‖(Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val ^ (j p) *
      star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) ^ (k p))‖)
        ≤ ∏ p, (N_c : ℝ) ^ (j p + k p) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ?_
          rw [norm_mul, norm_pow, norm_pow, norm_star, pow_add]
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
            (norm_trace_wilsonLine_le A _) _)
            (pow_le_pow_left₀ (norm_nonneg _)
              (norm_trace_wilsonLine_le A _) _)
            (by positivity) (by positivity)
      _ = (N_c : ℝ) ^ (∑ p, (j p + k p)) := by
          rw [Finset.prod_pow_eq_pow_sum]
  · exact Finset.prod_nonneg fun _ _ => norm_nonneg _

open Classical in
/-- The power-trace observable is **integrable**, with
`‖∫ powerTraceObservable‖ ≤ N_c^(1 + Σ(jₚ+kₚ))` — the survivor bound
of the exp-expanded area law (E4). -/
theorem norm_integral_powerTraceObservable_le
    (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖∫ A, powerTraceObservable es j k A
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) ^ (1 + ∑ p, (j p + k p)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))
    (MeasureTheory.ae_of_all _ fun A =>
      norm_powerTraceObservable_le A es j k)
  simpa using h

open Classical in
/-- The power-trace observable is integrable. -/
theorem integrable_powerTraceObservable (es : List (ConcreteEdge d N))
    (j k : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ) :
    Integrable (powerTraceObservable es j k)
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have h1 : Integrable (fun _ : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
    integrable_const 1
  have h2 := h1.bdd_mul
    (measurable_powerTraceObservable es j k).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun A =>
      norm_powerTraceObservable_le A es j k)
  simpa using h2

open Classical in
/-- **The per-multiplicity dichotomy** (exact-activity E4b-2a): the
`m`-th term of the exp-expanded Wilson integrand has expectation
EXACTLY ZERO below the area (binomial split + the multiplicity join)
and at most `N_c·∏(2δN_c)^{mₚ}/mₚ!` above it (direct bound). -/
theorem norm_integral_exp_term_le
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p, ((c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ^ (m p) / (Nat.factorial (m p) : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ if chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
          ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
        then (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
              / (Nat.factorial (m p) : ℝ)
        else 0 := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  by_cases hA : chainAreaA (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
      ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
  · -- survivors: direct bound, no expansion needed
    rw [if_pos hA]
    refine le_trans (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))
      (C := (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
        / (Nat.factorial (m p) : ℝ))
      (MeasureTheory.ae_of_all _ fun A => by
        rw [norm_mul, norm_prod]
        refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _)
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          fun p _ => ?_
        rw [norm_div, norm_pow, Complex.norm_natCast]
        have hz : ‖c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
            ≤ 2 * δ * (N_c : ℝ) := by
          have h1 : ‖c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
              ≤ δ * (N_c : ℝ) := by
            rw [norm_mul]
            exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
              (norm_nonneg _) hδ0
          have h2 : ‖c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
              ≤ δ * (N_c : ℝ) := by
            rw [norm_mul, norm_star]
            exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
              (norm_nonneg _) hδ0
          calc _ ≤ _ + _ := norm_add_le _ _
            _ ≤ 2 * δ * (N_c : ℝ) := by linarith
        gcongr)) ?_
    simp
  · -- below the area: binomial split + the multiplicity join kill
    rw [if_neg hA]
    have hzero : (∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p, ((c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ^ (m p) / (Nat.factorial (m p) : ℂ))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) = 0 := by
      have hpt : (fun A : GaugeConfig d N
          (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
          Matrix.trace (wilsonLine A es).val *
            ∏ p, ((c p * Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              + c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
                ^ (m p) / (Nat.factorial (m p) : ℂ)))
          = fun A => ∑ t ∈ Fintype.piFinset
              (fun p => Finset.range (m p + 1)),
            (∏ p, (c p ^ (t p) * c' p ^ (m p - t p) *
              (((m p).choose (t p) : ℂ)) / (Nat.factorial (m p) : ℂ))) *
              powerTraceObservable es t (fun p => m p - t p) A := by
        funext A
        rw [Finset.prod_congr rfl fun p _ => by
          rw [add_pow, Finset.sum_div]]
        rw [Finset.prod_univ_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        have hsplit : ∀ p : FiniteLatticeGeometry.P (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
            (c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
              ^ (t p) *
            (c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p - t p) *
            (((m p).choose (t p) : ℂ)) / (Nat.factorial (m p) : ℂ)
            = (c p ^ (t p) * c' p ^ (m p - t p) *
                (((m p).choose (t p) : ℂ)) / (Nat.factorial (m p) : ℂ)) *
              (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
                  ^ (t p) *
                star (Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
                  ^ (m p - t p)) := by
          intro p
          rw [mul_pow, mul_pow]
          ring
        rw [Finset.prod_congr rfl fun p _ => hsplit p]
        rw [Finset.prod_mul_distrib]
        have hpow_eq : powerTraceObservable es t (fun p => m p - t p) A
            = Matrix.trace (wilsonLine A es).val *
              ∏ p, (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
                  ^ (t p) *
                star (Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
                  ^ (m p - t p)) := rfl
        rw [hpow_eq]
        ring
      rw [hpt]
      rw [MeasureTheory.integral_finset_sum _ fun t _ =>
        (integrable_powerTraceObservable es t
          (fun p => m p - t p)).const_mul _]
      refine Finset.sum_eq_zero fun t ht => ?_
      refine (MeasureTheory.integral_const_mul _ _).trans ?_
      refine mul_eq_zero_of_right _ ?_
      by_contra hne
      have hbnd := chainAreaA_le_card_support_of_integral_pow_ne_zero
        es t (fun p => m p - t p) hne
      have hsupp_eq : (Finset.univ.filter
          (fun p => t p + (m p - t p) ≠ 0))
          = Finset.univ.filter (fun p => m p ≠ 0) := by
        refine Finset.filter_congr fun p _ => ?_
        have htp : t p ≤ m p := by
          have hmem := (Fintype.mem_piFinset.mp ht) p
          rw [Finset.mem_range] at hmem
          omega
        have : t p + (m p - t p) = m p := by omega
        rw [this]
      rw [hsupp_eq] at hbnd
      exact absurd hbnd hA
    rw [hzero, norm_zero]

open Classical in
/-- **The pinned-term dichotomy in SET form (VU campaign, V2-2):** the
indicator instantiation of the per-multiplicity dichotomy — a pinned
linear-activity term is EXACTLY ZERO below the `N`-ality area and at
most `N_c·(2δN_c)^{#S₀}` above it. -/
theorem norm_integral_pinned_term_le
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (S₀ : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) :
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p ∈ S₀, (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ if chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
          ≤ S₀.card
        then (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ S₀.card
        else 0 := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have h := norm_integral_exp_term_le es δ hδ0 c c' hc hc'
    (fun p => if p ∈ S₀ then 1 else 0)
  -- the indicator support is S₀
  have hsupp : (Finset.univ.filter
      (fun p => (if p ∈ S₀ then 1 else 0) ≠ 0)) = S₀ := by
    ext p
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, hne⟩
      by_contra hp
      exact hne (by rw [if_neg hp])
    · intro hp
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [if_pos hp]
      exact one_ne_zero
  -- the indicator product is the set product (ℂ side)
  have hprodC : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      (∏ p, ((c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
          ^ (if p ∈ S₀ then 1 else 0)
          / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℂ)))
      = ∏ p ∈ S₀, (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) := by
    intro A
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S₀),
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∏ p ∈ Finset.univ.filter (· ∉ S₀),
        ((c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ^ (if p ∈ S₀ then 1 else 0)
            / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℂ))
        = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hpn : p ∉ S₀ := (Finset.mem_filter.mp hp).2
      rw [if_neg hpn, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [h2, mul_one]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [if_pos hp, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  -- the indicator weight product is the set power (ℝ side)
  have hprodR : (∏ p, (2 * δ * (N_c : ℝ)) ^ (if p ∈ S₀ then 1 else 0)
      / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℝ))
      = (2 * δ * (N_c : ℝ)) ^ S₀.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S₀),
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∏ p ∈ Finset.univ.filter (· ∉ S₀),
        ((2 * δ * (N_c : ℝ)) ^ (if p ∈ S₀ then 1 else 0)
          / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℝ)) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hpn : p ∉ S₀ := (Finset.mem_filter.mp hp).2
      rw [if_neg hpn, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [h2, mul_one]
    have h3 : ∏ p ∈ S₀, ((2 * δ * (N_c : ℝ)) ^ (if p ∈ S₀ then 1 else 0)
        / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℝ))
        = ∏ _p ∈ S₀, (2 * δ * (N_c : ℝ)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [if_pos hp, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [h3, Finset.prod_const]
  rw [show (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ∏ p, ((c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ^ (if p ∈ S₀ then 1 else 0)
            / (Nat.factorial (if p ∈ S₀ then 1 else 0) : ℂ)))
    = fun A => Matrix.trace (wilsonLine A es).val *
        ∏ p ∈ S₀, (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
    from funext fun A => by rw [hprodC A]] at h
  rw [hsupp, hprodR] at h
  exact h

set_option maxHeartbeats 1000000 in
open Classical in
/-- **THE EXACT-ACTIVITY FINITE-VOLUME AREA LAW** (E4b-2, campaign
headline).  For the TRUE Wilson Boltzmann factor `∏_p exp(zₚ)`,
`zₚ = cₚ·tr Hₚ + cₚ'·conj tr Hₚ` with `‖cₚ‖, ‖cₚ'‖ ≤ δ`:

`‖∫ tr(W_C)·∏ₚ exp(zₚ)‖
   ≤ N_c · 2^{#P} · (e^{2δN_c}−1)^{Area(C)} · (e^{2δN_c})^{#P}`.

NO smallness hypothesis — valid for every `δ ≥ 0`; the
`(e^{2δN_c}−1)^{Area}` factor decays as `(2δN_c)^{Area}` at strong
coupling, recovering the linearized area law.  Route: pointwise
exp-series (`prod_exp_eq_tsum_prod_pow`) → `∫↔∑'` swap
(`integral_tsum_of_bounded`) → per-multiplicity dichotomy
(`norm_integral_exp_term_le`) → constrained-Pi tail
(`tsum_constrained_prod_pow_div_factorial_le`). -/
theorem finite_volume_area_law_exp
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p, Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) *
          (2 ^ (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) *
            ((Real.exp (2 * δ * (N_c : ℝ)) - 1)
                ^ (chainAreaA (R := ZMod N_c) (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
                  (loopChain (R := ZMod N_c) (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) *
              Real.exp (2 * δ * (N_c : ℝ))
                ^ (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))))) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have hx0 : (0 : ℝ) ≤ 2 * δ * (N_c : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hδ0) (Nat.cast_nonneg _)
  -- measurability of each multiplicity term
  have hFm : ∀ m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
      Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        Matrix.trace (wilsonLine A es).val *
          ∏ p, ((c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p) / (Nat.factorial (m p) : ℂ))) := by
    intro m
    refine (measurable_trace_wilsonLine es).mul
      (Finset.measurable_prod _ ?_)
    intro p _
    exact Measurable.div_const
      ((((measurable_trace_wilsonLine _).const_mul (c p)).add
        (((continuous_star.measurable).comp
          (measurable_trace_wilsonLine _)).const_mul (c' p))).pow_const _) _
  -- pointwise domination by the exponential weights
  have hFb : ∀ (m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ)
      (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))),
      ‖Matrix.trace (wilsonLine A es).val *
        ∏ p, ((c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ^ (m p) / (Nat.factorial (m p) : ℂ))‖
      ≤ (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
          / (Nat.factorial (m p) : ℝ) := by
    intro m A
    rw [norm_mul, norm_prod]
    refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _)
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have h1 : ‖c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
        ≤ δ * (N_c : ℝ) := by
      rw [norm_mul]
      exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
        (norm_nonneg _) hδ0
    have h2 : ‖c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
        ≤ δ * (N_c : ℝ) := by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
        (norm_nonneg _) hδ0
    have hz : ‖c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
        ≤ 2 * δ * (N_c : ℝ) := by
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 * δ * (N_c : ℝ) := by linarith
    gcongr
  -- weight nonnegativity and summability
  have hcw : ∀ m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
      (0 : ℝ) ≤ (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
        / (Nat.factorial (m p) : ℝ) := fun m =>
    mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun p _ =>
      div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
  have hcs : Summable (fun m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ =>
      (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
        / (Nat.factorial (m p) : ℝ)) :=
    (summable_prod_pow_div_factorial (2 * δ * (N_c : ℝ)) hx0).mul_left _
  -- pointwise exp-series, loop trace pulled inside the sum
  have hpt : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ∏ p, Complex.exp (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      = fun A => ∑' m : FiniteLatticeGeometry.P (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
          Matrix.trace (wilsonLine A es).val *
            ∏ p, ((c p * Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              + c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
                ^ (m p) / (Nat.factorial (m p) : ℂ)) := by
    funext A
    rw [prod_exp_eq_tsum_prod_pow]
    exact tsum_mul_left.symm
  -- the ∫ ↔ ∑' swap (expected-type driven)
  have hswap : (∫ A, ∑' m : FiniteLatticeGeometry.P (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
        Matrix.trace (wilsonLine A es).val *
          ∏ p, ((c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p) / (Nat.factorial (m p) : ℂ))
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      = ∑' m : FiniteLatticeGeometry.P (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
          ∫ A, Matrix.trace (wilsonLine A es).val *
          ∏ p, ((c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p) / (Nat.factorial (m p) : ℂ))
            ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
    integral_tsum_of_bounded _ _ _ hFm hFb hcw hcs
  rw [hpt, hswap]
  -- per-term dichotomy
  have hdich : ∀ m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ,
      ‖∫ A, Matrix.trace (wilsonLine A es).val *
          ∏ p, ((c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p) / (Nat.factorial (m p) : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
        ≤ if chainAreaA (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
              (loopChain (R := ZMod N_c) (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
            ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
          then (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
                / (Nat.factorial (m p) : ℝ)
          else 0 :=
    fun m => norm_integral_exp_term_le es δ hδ0 c c' hc hc' m
  have hite : Summable (fun m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ =>
      if chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
          ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
        then (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
              / (Nat.factorial (m p) : ℝ)
        else 0) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hcs
    · split_ifs
      · exact hcw m
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hcw m
  have hnorms : Summable (fun m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ =>
      ‖∫ A, Matrix.trace (wilsonLine A es).val *
          ∏ p, ((c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ^ (m p) / (Nat.factorial (m p) : ℂ))
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hdich hite
  refine le_trans (norm_tsum_le_tsum_norm hnorms) ?_
  refine le_trans (hnorms.tsum_le_tsum hdich hite) ?_
  -- factor `N_c` out and apply the constrained-Pi tail estimate
  have hfac : (fun m : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℕ =>
      if chainAreaA (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
          ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
        then (N_c : ℝ) * ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
              / (Nat.factorial (m p) : ℝ)
        else 0)
      = fun m => (N_c : ℝ) *
          (if chainAreaA (R := ZMod N_c) (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
                (loopChain (R := ZMod N_c) (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)
              ≤ (Finset.univ.filter (fun p => m p ≠ 0)).card
            then ∏ p, (2 * δ * (N_c : ℝ)) ^ (m p)
                  / (Nat.factorial (m p) : ℝ)
            else 0) := by
    funext m
    split_ifs
    · rfl
    · rw [mul_zero]
  rw [hfac, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (tsum_constrained_prod_pow_div_factorial_le (2 * δ * (N_c : ℝ)) hx0 _)
    (Nat.cast_nonneg _)

/-! ## AL6-1: the per-term kill in `Finset` form

The powerset expansion of `⟨W_C⟩·Z` produces terms indexed by a
plaquette set `S` and a holomorphic choice `T ⊆ S`; this is the join
restated in exactly that shape: such a term vanishes whenever `S` is
too small to span the loop. -/

open Classical in
/-- **The expansion-term kill:** a strong-coupling expansion term —
the Wilson loop times holomorphic plaquette traces over `T` and
antiholomorphic ones over `S \ T` — has zero β = 0 expectation
whenever `|S|` is smaller than the loop's `N`-ality area. -/
theorem integral_trace_mul_prod_traces_eq_zero
    (es : List (ConcreteEdge d N))
    (S T : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) (hTS : T ⊆ S)
    (hlt : S.card < chainAreaA (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) :
    ∫ A, Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) = 0 := by
  classical
  set ps : Fin S.card → FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :=
    fun i => (S.equivFin.symm i : _) with hps
  set σb : Fin S.card → Bool := fun i => decide (ps i ∈ T) with hσb
  -- rewrite the integrand into the join's family form
  have hint : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      = fun A => ∏ j : Fin (S.card + 1),
          Matrix.trace (wilsonLine A
            (Fin.cons (α := fun _ => List (ConcreteEdge d N)) es (fun i =>
              if σb i
              then plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
              else ((plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                  (FiniteLatticeGeometry.reverse (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)
              j)).val := by
    funext A
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    -- the m plaquette factors: per-i decoration, then reindex to `S`
    have hper : ∀ i : Fin S.card,
        Matrix.trace (wilsonLine A
          (if σb i
            then plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)
            else ((plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i)).map
                (FiniteLatticeGeometry.reverse (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse)).val
        = (if ps i ∈ T
            then Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i))).val
            else star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i))).val)) := by
      intro i
      by_cases hm : ps i ∈ T
      · rw [if_pos hm, if_pos (by simp [hσb, hm])]
      · rw [if_neg hm, if_neg (by simp [hσb, hm]),
          star_trace_wilsonLine]
    rw [Finset.prod_congr rfl fun i _ => hper i]
    -- reindex `Fin S.card` to `S`
    have hre : (∏ i : Fin S.card,
        (if ps i ∈ T
          then Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i))).val
          else star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (ps i))).val)))
        = ∏ p ∈ S,
          (if p ∈ T
            then Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            else star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)) := by
      refine Eq.trans ?_ (Finset.prod_coe_sort S _)
      exact Fintype.prod_equiv S.equivFin.symm _ _ fun i => by rw [hps]
    rw [hre, Finset.prod_ite]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTS]
    · rw [show S.filter (fun p => p ∉ T) = S \ T from
        (Finset.sdiff_eq_filter S T).symm]
  rw [hint]
  by_contra hne
  exact absurd
    (chainAreaA_loopChain_le_of_integral_ne_zero es ps σb hne)
    (not_le.mpr hlt)

/-! ## AL6-2a: the surviving-term toolkit -/

open Classical in
/-- The `(S, T)`-expansion term is **measurable**. -/
theorem measurable_trace_mul_prod_traces
    (es : List (ConcreteEdge d N))
    (S T : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) :
    Measurable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))) := by
  refine (measurable_trace_wilsonLine es).mul (Measurable.mul ?_ ?_)
  · exact Finset.measurable_prod _ fun p _ =>
      measurable_trace_wilsonLine _
  · exact Finset.measurable_prod _ fun p _ =>
      (continuous_star.measurable).comp (measurable_trace_wilsonLine _)

open Classical in
/-- The `(S, T)`-expansion term is **pointwise bounded by
`N_c^(|S|+1)`**. -/
theorem norm_trace_mul_prod_traces_le
    (A : GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
    (es : List (ConcreteEdge d N))
    (S T : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) (hTS : T ⊆ S) :
    ‖Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))‖
      ≤ (N_c : ℝ) ^ (S.card + 1) := by
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  have h1 : (∏ p ∈ T, ‖Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖)
      ≤ (N_c : ℝ) ^ T.card := by
    calc (∏ p ∈ T, ‖Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖)
        ≤ ∏ _p ∈ T, (N_c : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun p _ => norm_trace_wilsonLine_le A _)
      _ = (N_c : ℝ) ^ T.card := Finset.prod_const _
  have h2 : (∏ p ∈ S \ T, ‖star (Matrix.trace (wilsonLine A
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖)
      ≤ (N_c : ℝ) ^ (S \ T).card := by
    calc (∏ p ∈ S \ T, ‖star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖)
        ≤ ∏ _p ∈ S \ T, (N_c : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun p _ => by rw [norm_star]; exact norm_trace_wilsonLine_le A _)
      _ = (N_c : ℝ) ^ (S \ T).card := Finset.prod_const _
  have hcard : T.card + (S \ T).card = S.card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hTS
  have hN0 : (0 : ℝ) ≤ (N_c : ℝ) := Nat.cast_nonneg _
  calc ‖Matrix.trace (wilsonLine A es).val‖ *
        ((∏ p ∈ T, ‖Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖) *
          ∏ p ∈ S \ T, ‖star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖)
      ≤ (N_c : ℝ) * ((N_c : ℝ) ^ T.card * (N_c : ℝ) ^ (S \ T).card) := by
        refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_
          (by positivity) hN0
        exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (by positivity)
    _ = (N_c : ℝ) ^ (S.card + 1) := by
        rw [← pow_add, hcard, ← pow_succ']

open Classical in
/-- The `(S, T)`-expansion term is **integrable**. -/
theorem integrable_trace_mul_prod_traces
    (es : List (ConcreteEdge d N))
    (S T : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) (hTS : T ⊆ S) :
    Integrable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  have h1 : Integrable (fun _ : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
    integrable_const 1
  have h2 := h1.bdd_mul
    (measurable_trace_mul_prod_traces es S T).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun A =>
      norm_trace_mul_prod_traces_le A es S T hTS)
  simpa using h2

open Classical in
/-- **The surviving-term bound:** every `(S, T)`-expansion term has
β = 0 expectation of norm at most `N_c^(|S|+1)`. -/
theorem norm_integral_trace_mul_prod_traces_le
    (es : List (ConcreteEdge d N))
    (S T : Finset (FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) (hTS : T ⊆ S) :
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ((∏ p ∈ T, Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
          ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) ^ (S.card + 1) := by
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))
    (MeasureTheory.ae_of_all _ fun A =>
      norm_trace_mul_prod_traces_le A es S T hTS)
  simpa using h

/-! ## AL6-2b: THE FINITE-VOLUME AREA LAW -/

open Classical in
/-- **The finite-volume area law** for linearized activities: with
plaquette couplings of size `≤ δ` and `2δN_c ≤ 1`, the full β-expanded
Wilson-loop expectation obeys

    `‖∫ tr(W_C)·∏_p(1 + cₚ·tr Hₚ + cₚ'·conj tr Hₚ)‖
        ≤ N_c · 2^{#P} · (2δN_c)^{Area}`

with `Area = chainAreaA (loopChain C)` the `N`-ality area.  Every
sub-area term of the expansion vanishes EXACTLY
(`integral_trace_mul_prod_traces_eq_zero`); the surviving terms are
counted crudely (`2^{#P}`, finite volume) and bounded by
`norm_integral_trace_mul_prod_traces_le`. -/
theorem finite_volume_area_law
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (hsmall : 2 * δ * (N_c : ℝ) ≤ 1) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖∫ A, Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) *
          2 ^ (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) *
          (2 * δ * (N_c : ℝ)) ^ (chainAreaA (R := ZMod N_c) (d := d)
            (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  set Ar := chainAreaA (R := ZMod N_c) (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    (loopChain (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es) with hAr
  have hN0 : (0 : ℝ) ≤ (N_c : ℝ) := Nat.cast_nonneg _
  have h2δN0 : (0 : ℝ) ≤ 2 * δ * (N_c : ℝ) := by positivity
  -- the activity functions and their bounds
  set f : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) →
      GaugeConfig d N (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ :=
    fun p A => c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
      + c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)
    with hf
  have hfm : ∀ p, Measurable (f p) := by
    intro p
    exact ((measurable_trace_wilsonLine _).const_mul _).add
      (((continuous_star.measurable).comp
        (measurable_trace_wilsonLine _)).const_mul _)
  have hfb : ∀ p A, ‖f p A‖ ≤ 2 * δ * (N_c : ℝ) := by
    intro p A
    have h1 : ‖c p * Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
        ≤ δ * (N_c : ℝ) := by
      rw [norm_mul]
      exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
        (norm_nonneg _) hδ0
    have h2 : ‖c' p * star (Matrix.trace (wilsonLine A
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
        ≤ δ * (N_c : ℝ) := by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
        (norm_nonneg _) hδ0
    calc ‖f p A‖ ≤ ‖c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
        + ‖c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖ :=
          norm_add_le _ _
      _ ≤ 2 * δ * (N_c : ℝ) := by linarith
  -- the powerset expansion
  have hexp := integral_mul_prod_one_add
    (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))
    (Finset.univ)
    (fun A => Matrix.trace (wilsonLine A es).val) f
    (measurable_trace_wilsonLine es) (N_c : ℝ)
    (fun A => norm_trace_wilsonLine_le A es)
    hfm (2 * δ * (N_c : ℝ)) hfb
  rw [show (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))))
      = fun A => Matrix.trace (wilsonLine A es).val *
          ∏ p, (1 + f p A) from rfl]
  rw [hexp]
  -- the per-S σ-split
  have hA : ∀ S ∈ (Finset.univ : Finset (FiniteLatticeGeometry.P (d := d)
      (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).powerset,
      (∫ A, Matrix.trace (wilsonLine A es).val * ∏ p ∈ S, f p A
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      = ∑ T ∈ S.powerset,
          ((∏ p ∈ T, c p) * ∏ p ∈ S \ T, c' p) *
            ∫ A, Matrix.trace (wilsonLine A es).val *
              ((∏ p ∈ T, Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
                ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
    intro S _
    have hpt : (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
        Matrix.trace (wilsonLine A es).val * ∏ p ∈ S, f p A)
        = fun A => ∑ T ∈ S.powerset,
            ((∏ p ∈ T, c p) * ∏ p ∈ S \ T, c' p) *
              (Matrix.trace (wilsonLine A es).val *
                ((∏ p ∈ T, Matrix.trace (wilsonLine A
                    (plaquetteList (d := d) (N := N)
                      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
                  ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
                    (plaquetteList (d := d) (N := N)
                      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))) := by
      funext A
      simp only [hf]
      rw [Finset.prod_add, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finset_sum _ fun T hT =>
      ((integrable_trace_mul_prod_traces es S T
        (Finset.mem_powerset.mp hT)).const_mul _)]
    exact Finset.sum_congr rfl fun T _ =>
      MeasureTheory.integral_const_mul _ _
  rw [Finset.sum_congr rfl hA]
  -- triangle inequality, per-S classification, crude count
  refine le_trans (norm_sum_le _ _) ?_
  have hperS : ∀ S ∈ (Finset.univ : Finset (FiniteLatticeGeometry.P
      (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).powerset,
      ‖∑ T ∈ S.powerset,
        ((∏ p ∈ T, c p) * ∏ p ∈ S \ T, c' p) *
          ∫ A, Matrix.trace (wilsonLine A es).val *
            ((∏ p ∈ T, Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
              ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
            ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ Ar := by
    intro S _
    by_cases hS : S.card < Ar
    · -- every term killed
      rw [Finset.sum_eq_zero fun T hT => by
        rw [integral_trace_mul_prod_traces_eq_zero es S T
          (Finset.mem_powerset.mp hT) hS, mul_zero]]
      simp only [norm_zero]
      positivity
    · push_neg at hS
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ T ∈ S.powerset,
          ‖((∏ p ∈ T, c p) * ∏ p ∈ S \ T, c' p) *
            ∫ A, Matrix.trace (wilsonLine A es).val *
              ((∏ p ∈ T, Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val) *
                ∏ p ∈ S \ T, star (Matrix.trace (wilsonLine A
                  (plaquetteList (d := d) (N := N)
                    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))
              ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
          ≤ δ ^ S.card * (N_c : ℝ) ^ (S.card + 1) := by
        intro T hT
        have hTS := Finset.mem_powerset.mp hT
        rw [norm_mul, norm_mul]
        have hcT : ‖∏ p ∈ T, c p‖ ≤ δ ^ T.card := by
          rw [norm_prod]
          calc ∏ p ∈ T, ‖c p‖ ≤ ∏ _p ∈ T, δ :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  (fun p _ => hc p)
            _ = δ ^ T.card := Finset.prod_const _
        have hcT' : ‖∏ p ∈ S \ T, c' p‖ ≤ δ ^ (S \ T).card := by
          rw [norm_prod]
          calc ∏ p ∈ S \ T, ‖c' p‖ ≤ ∏ _p ∈ S \ T, δ :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  (fun p _ => hc' p)
            _ = δ ^ (S \ T).card := Finset.prod_const _
        have hcards : T.card + (S \ T).card = S.card := by
          rw [add_comm]
          exact Finset.card_sdiff_add_card_eq_card hTS
        calc ‖∏ p ∈ T, c p‖ * ‖∏ p ∈ S \ T, c' p‖ * _
            ≤ (δ ^ T.card * δ ^ (S \ T).card) * (N_c : ℝ) ^ (S.card + 1) := by
              refine mul_le_mul (mul_le_mul hcT hcT' (norm_nonneg _)
                (by positivity)) (norm_integral_trace_mul_prod_traces_le
                  es S T hTS) (norm_nonneg _) (by positivity)
          _ = δ ^ S.card * (N_c : ℝ) ^ (S.card + 1) := by
              rw [← pow_add, hcards]
      calc (∑ T ∈ S.powerset, ‖_‖)
          ≤ ∑ _T ∈ S.powerset, δ ^ S.card * (N_c : ℝ) ^ (S.card + 1) :=
            Finset.sum_le_sum hterm
        _ = 2 ^ S.card * (δ ^ S.card * (N_c : ℝ) ^ (S.card + 1)) := by
            rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
            push_cast
            ring
        _ = (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ S.card := by
            rw [mul_pow, mul_pow, pow_succ]
            ring
        _ ≤ (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ Ar := by
            refine mul_le_mul_of_nonneg_left ?_ hN0
            exact pow_le_pow_of_le_one h2δN0 hsmall hS
  calc (∑ S ∈ (Finset.univ : Finset (FiniteLatticeGeometry.P (d := d)
        (N := N) (G := ↥(Matrix.specialUnitaryGroup
          (Fin N_c) ℂ)))).powerset, ‖_‖)
      ≤ ∑ _S ∈ (Finset.univ : Finset (FiniteLatticeGeometry.P (d := d)
          (N := N) (G := ↥(Matrix.specialUnitaryGroup
            (Fin N_c) ℂ)))).powerset,
          (N_c : ℝ) * (2 * δ * (N_c : ℝ)) ^ Ar :=
        Finset.sum_le_sum hperS
    _ = (N_c : ℝ) * 2 ^ (Fintype.card (FiniteLatticeGeometry.P (d := d)
          (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) *
        (2 * δ * (N_c : ℝ)) ^ Ar := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ,
          nsmul_eq_mul]
        push_cast
        ring

open Classical in
/-- The full strong-coupling integrand is integrable — needed to
split the `Re tr` observable into its holomorphic halves. -/
theorem integrable_trace_mul_prod_one_add
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    Integrable (fun A : GaugeConfig d N
        (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  have hm : Measurable (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))) := by
    refine (measurable_trace_wilsonLine es).mul
      (Finset.measurable_prod _ fun p _ => Measurable.const_add ?_ 1)
    exact ((measurable_trace_wilsonLine _).const_mul _).add
      (((continuous_star.measurable).comp
        (measurable_trace_wilsonLine _)).const_mul _)
  have hb : ∀ A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
      ‖Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))‖
      ≤ (N_c : ℝ) * (1 + 2 * δ * (N_c : ℝ)) ^ (Fintype.card
          (FiniteLatticeGeometry.P (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) := by
    intro A
    rw [norm_mul]
    refine mul_le_mul (norm_trace_wilsonLine_le A es) ?_ (norm_nonneg _)
      (Nat.cast_nonneg _)
    rw [norm_prod]
    calc (∏ p, ‖(1 + (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))‖)
        ≤ ∏ _p : FiniteLatticeGeometry.P (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)),
            (1 + 2 * δ * (N_c : ℝ)) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ?_
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_one]
          have h1 : ‖c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              + c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
              ≤ 2 * δ * (N_c : ℝ) := by
            refine le_trans (norm_add_le _ _) ?_
            have ha : ‖c p * Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val‖
                ≤ δ * (N_c : ℝ) := by
              rw [norm_mul]
              exact mul_le_mul (hc p) (norm_trace_wilsonLine_le A _)
                (norm_nonneg _) hδ0
            have hb' : ‖c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)‖
                ≤ δ * (N_c : ℝ) := by
              rw [norm_mul, norm_star]
              exact mul_le_mul (hc' p) (norm_trace_wilsonLine_le A _)
                (norm_nonneg _) hδ0
            linarith
          linarith
      _ = (1 + 2 * δ * (N_c : ℝ)) ^ (Fintype.card
            (FiniteLatticeGeometry.P (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) := by
          rw [Finset.prod_const, Finset.card_univ]
  have h1 : Integrable (fun _ : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => (1 : ℂ))
      (gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)) :=
    integrable_const 1
  have h2 := h1.bdd_mul hm.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ hb)
  simpa using h2

open Classical in
/-- **The finite-volume area law for the PHYSICAL observable
`Re tr(W_C)`:** the real-part Wilson loop is the average of the loop
and its reversal, and the reversal has the SAME `N`-ality area
(`loopChain_reverse_list` + `chainAreaA_neg`), so the bound carries
over unchanged. -/
theorem finite_volume_area_law_re
    (es : List (ConcreteEdge d N)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (c c' : FiniteLatticeGeometry.P (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ δ) (hc' : ∀ p, ‖c' p‖ ≤ δ)
    (hsmall : 2 * δ * (N_c : ℝ) ≤ 1) :
    letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
    ‖∫ A, (((Matrix.trace (wilsonLine A es).val).re : ℝ) : ℂ) *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))‖
      ≤ (N_c : ℝ) *
          2 ^ (Fintype.card (FiniteLatticeGeometry.P (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))) *
          (2 * δ * (N_c : ℝ)) ^ (chainAreaA (R := ZMod N_c) (d := d)
            (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
            (loopChain (R := ZMod N_c) (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es)) := by
  letI := FiniteLatticeGeometry.fintypeP (d := d) (N := N)
    (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
  set es_rev : List (ConcreteEdge d N) :=
    (es.map (FiniteLatticeGeometry.reverse (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))).reverse
    with hes_rev
  have hbound1 := finite_volume_area_law es δ hδ0 c c' hc hc' hsmall
  have hbound2 := finite_volume_area_law es_rev δ hδ0 c c' hc hc' hsmall
  have hAr : chainAreaA (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es_rev)
      = chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es) := by
    have h1 : loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es_rev
        = fun e => - loopChain (R := ZMod N_c) (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) es e :=
      funext fun e => loopChain_reverse_list es e
    rw [h1, chainAreaA_neg]
  rw [hAr] at hbound2
  have hI1 := integrable_trace_mul_prod_one_add es δ hδ0 c c' hc hc'
  have hI2 := integrable_trace_mul_prod_one_add es_rev δ hδ0 c c' hc hc'
  -- split the real part into the two holomorphic halves
  have hpt : (fun A : GaugeConfig d N
      (↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) =>
      (((Matrix.trace (wilsonLine A es).val).re : ℝ) : ℂ) *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val))))
      = fun A => (1 / 2 : ℂ) *
          (Matrix.trace (wilsonLine A es).val *
            ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              + c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
          + Matrix.trace (wilsonLine A es_rev).val *
            ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
              + c' p * star (Matrix.trace (wilsonLine A
                (plaquetteList (d := d) (N := N)
                  (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))) := by
    funext A
    have hrev : Matrix.trace (wilsonLine A es_rev).val
        = star (Matrix.trace (wilsonLine A es).val) :=
      star_trace_wilsonLine A es
    have hre : (((Matrix.trace (wilsonLine A es).val).re : ℝ) : ℂ)
        = (Matrix.trace (wilsonLine A es).val
            + star (Matrix.trace (wilsonLine A es).val)) / 2 := by
      have := Complex.add_conj (Matrix.trace (wilsonLine A es).val)
      rw [show (starRingEnd ℂ) (Matrix.trace (wilsonLine A es).val)
          = star (Matrix.trace (wilsonLine A es).val) from rfl] at this
      rw [this]
      push_cast
      ring
    rw [hrev, hre]
    ring
  rw [hpt]
  have hadd : (∫ A, ((1 / 2 : ℂ) *
      (Matrix.trace (wilsonLine A es).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      + Matrix.trace (wilsonLine A es_rev).val *
        ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
          + c' p * star (Matrix.trace (wilsonLine A
            (plaquetteList (d := d) (N := N)
              (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))))
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
      = (1 / 2 : ℂ) *
        ((∫ A, Matrix.trace (wilsonLine A es).val *
          ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))
        + ∫ A, Matrix.trace (wilsonLine A es_rev).val *
          ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
            + c' p * star (Matrix.trace (wilsonLine A
              (plaquetteList (d := d) (N := N)
                (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
          ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c))) := by
    refine (MeasureTheory.integral_const_mul _ _).trans ?_
    congr 1
    exact MeasureTheory.integral_add hI1 hI2
  rw [hadd, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  refine le_trans (mul_le_mul_of_nonneg_left
    (norm_add_le _ _) (by norm_num)) ?_
  have htot := add_le_add hbound1 hbound2
  nlinarith [hbound1, hbound2, norm_nonneg
    (∫ A, Matrix.trace (wilsonLine A es).val *
      ∏ p, (1 + (c p * Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val
        + c' p * star (Matrix.trace (wilsonLine A
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)).val)))
      ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb N_c)))]

/-! ## The concrete non-vacuity witness: plaquette loops have area ≥ 1 -/

/-- Shifting a lattice site moves it (for `N ≥ 2`). -/
theorem FinBox.shift_ne {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (x : FinBox d N) (i : Fin d) : x.shift i ≠ x := by
  intro h
  have h1 := congrFun h i
  simp only [FinBox.shift, if_pos rfl] at h1
  have hval : ((x i : ℕ) + 1) % N = (x i : ℕ) := by
    have h2 := congrArg Fin.val h1
    exact h2
  have hlt := (x i).isLt
  rcases Nat.lt_or_ge ((x i : ℕ) + 1) N with hc | hc
  · rw [Nat.mod_eq_of_lt hc] at hval
    omega
  · have heq : (x i : ℕ) + 1 = N := by omega
    rw [heq, Nat.mod_self] at hval
    omega

open Classical in
/-- **The plaquette boundary's chain is nonzero** (concrete geometry,
`N ≥ 2`, `N_c ≥ 2`): the chain takes value `1` at the plaquette's
first edge — the four edges are distinct and none is the reverse of
the first. -/
theorem loopChain_plaquetteList_ne_zero (hN2 : 2 ≤ N) (hNc : 2 ≤ N_c)
    (p : ConcretePlaquette d N) :
    loopChain (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (plaquetteList (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p) ≠ 0 := by
  haveI : Fact (1 < N_c) := ⟨hNc⟩
  intro h
  have h0 := congrFun h (FiniteLatticeGeometry.plaquetteEdge
    (d := d) (N := N) (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p 0)
  -- the inequality facts among the four edges
  have hd : p.dir1 ≠ p.dir2 := Fin.ne_of_lt p.hlt
  have hshift : p.site.shift p.dir2 ≠ p.site :=
    FinBox.shift_ne hN2 p.site p.dir2
  -- evaluate the chain at the first edge: count 1 forward, 0 backward
  have hval : loopChain (R := ZMod N_c) (d := d) (N := N)
      (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
      (plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)
      (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p 0)
      = 1 := by
    show ((List.count _ _ : ℕ) : ZMod N_c) - ((List.count _ _ : ℕ) : ZMod N_c) = 1
    rw [show (FiniteLatticeGeometry.reverse (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p 0))
      = ⟨p.site, p.dir1, false⟩ from rfl]
    rw [show (FiniteLatticeGeometry.plaquetteEdge (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p 0)
      = ⟨p.site, p.dir1, true⟩ from rfl]
    rw [show plaquetteList (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p
      = [⟨p.site, p.dir1, true⟩,
         ⟨p.site.shift p.dir1, p.dir2, true⟩,
         ⟨p.site.shift p.dir2, p.dir1, false⟩,
         ⟨p.site, p.dir2, false⟩] from rfl]
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    have q1 : ¬ (({ source := p.site, dir := p.dir2, sign := false } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := true }) :=
      fun hq => hd (congrArg ConcreteEdge.dir hq).symm
    have q2 : ¬ (({ source := (p.site.shift p.dir2), dir := p.dir1, sign := false } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := true }) :=
      fun hq => Bool.noConfusion (congrArg ConcreteEdge.sign hq)
    have q3 : ¬ (({ source := (p.site.shift p.dir1), dir := p.dir2, sign := true } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := true }) :=
      fun hq => hd (congrArg ConcreteEdge.dir hq).symm
    have q4 : ¬ (({ source := p.site, dir := p.dir2, sign := false } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := false }) :=
      fun hq => hd (congrArg ConcreteEdge.dir hq).symm
    have q5 : ¬ (({ source := (p.site.shift p.dir2), dir := p.dir1, sign := false } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := false }) :=
      fun hq => hshift (congrArg ConcreteEdge.source hq)
    have q6 : ¬ (({ source := (p.site.shift p.dir1), dir := p.dir2, sign := true } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := false }) :=
      fun hq => Bool.noConfusion (congrArg ConcreteEdge.sign hq)
    have q7 : ¬ (({ source := p.site, dir := p.dir1, sign := true } :
        FiniteLatticeGeometry.E (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)))
        = { source := p.site, dir := p.dir1, sign := false }) :=
      fun hq => Bool.noConfusion (congrArg ConcreteEdge.sign hq)
    simp only [if_neg q1, if_neg q2, if_neg q3, if_neg q4, if_neg q5,
      if_neg q6, if_neg q7]
    simp
  rw [hval] at h0
  rw [Pi.zero_apply] at h0
  exact one_ne_zero h0

open Classical in
/-- **The witness:** every concrete plaquette-boundary loop has
`N`-ality area at least `1` — the area-law exponent is genuinely
positive on actual loops.  Closes the adversarial non-vacuity audit
of `finite_volume_area_law`. -/
theorem one_le_chainAreaA_plaquette (hN2 : 2 ≤ N) (hNc : 2 ≤ N_c)
    (p : ConcretePlaquette d N) :
    1 ≤ chainAreaA (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
        (loopChain (R := ZMod N_c) (d := d) (N := N)
          (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ))
          (plaquetteList (d := d) (N := N)
            (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p)) :=
  one_le_chainAreaA (loopChain_plaquetteList_ne_zero hN2 hNc p)
    ⟨fun q => if q = p then (1 : ZMod N_c) else 0,
      chainBoundary₂A_single (R := ZMod N_c) (d := d) (N := N)
        (G := ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) p⟩

end YangMills
