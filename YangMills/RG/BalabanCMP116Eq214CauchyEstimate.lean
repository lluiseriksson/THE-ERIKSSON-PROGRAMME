/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalTerm

/-!
# CMP116 equation (2.14): quantitative Cauchy-family estimates

This module supplies the first analytic majorant used toward (2.26).  It
bounds the literal interpolation/Cauchy operator, rather than replacing it by
an abstract derivative estimate.

The recursive boundary predicate follows the actual source order.  At every
coordinate it quantifies over the interpolation segment and the corresponding
complex circle, while retaining arbitrary dependence on all later
coordinates.  The terminal two-family theorem therefore applies directly to
the nested `σ(Δ)` and `τ(Y)` operators in equation (2.14).
-/

namespace YangMills.RG

open Set Metric MeasureTheory Complex intervalIntegral
open scoped Real Topology

/-- Recursive numerical loss from the successive Cauchy circles. -/
noncomputable def cmp116Eq214CauchyRate :
    (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ
  | 0, _, M => M
  | n + 1, radius, M =>
      cmp116Eq214CauchyRate n (fun i => radius i.succ) M / radius 0

/-- Uniform boundary bound on every nested source-ordered Cauchy contour. -/
def CMP116Eq214CauchyBoundaryBound :
    (n : ℕ) → (Fin n → ℝ) → ((Fin n → ℂ) → ℂ) → ℝ → Prop
  | 0, _, F, M => ‖F Fin.elim0‖ ≤ M
  | n + 1, radius, F, M =>
      ∀ s ∈ Set.uIoc (0 : ℝ) 1,
        ∀ z ∈ Metric.sphere (s : ℂ) (radius 0),
          CMP116Eq214CauchyBoundaryBound n (fun i => radius i.succ)
            (fun tail => F (Fin.cons z tail)) M

/-- One Cauchy/interpolation coordinate costs exactly one inverse radius. -/
theorem norm_cmp116Eq214CauchyStep_le_div
    {radius M : ℝ} {f : ℂ → ℂ}
    (hradius : 0 < radius)
    (hf : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ∀ z ∈ Metric.sphere (s : ℂ) radius, ‖f z‖ ≤ M) :
    ‖cmp116Eq214CauchyStep radius f‖ ≤ M / radius := by
  unfold cmp116Eq214CauchyStep
  calc
    ‖∫ s : ℝ in (0 : ℝ)..1, Complex.cderiv radius f (s : ℂ)‖ ≤
        (M / radius) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
        Complex.norm_cderiv_le hradius (hf s hs)
    _ = M / radius := by norm_num

/-- Iterating the preceding estimate preserves all cross-coordinate
dependence and accumulates precisely the recursive inverse-radius loss. -/
theorem norm_cmp116Eq214CauchyFamily_le_rate
    (n : ℕ) (radius : Fin n → ℝ)
    (F : (Fin n → ℂ) → ℂ) (M : ℝ)
    (hradius : ∀ i, 0 < radius i)
    (hF : CMP116Eq214CauchyBoundaryBound n radius F M) :
    ‖cmp116Eq214CauchyFamily n radius F‖ ≤
      cmp116Eq214CauchyRate n radius M := by
  induction n with
  | zero =>
      simpa [cmp116Eq214CauchyFamily, cmp116Eq214CauchyRate,
        CMP116Eq214CauchyBoundaryBound] using hF
  | succ n ih =>
      rw [cmp116Eq214CauchyFamily_succ]
      apply norm_cmp116Eq214CauchyStep_le_div (hradius 0)
      intro s hs z hz
      apply ih
      · intro i
        exact hradius i.succ
      · exact hF s hs z hz

/-- Joint boundary condition for the `σ(Δ)` family outside the `τ(Y)`
family in equation (2.14). -/
def CMP116Eq214NestedCauchyBoundaryBound :
    (nDelta nY : ℕ) →
      (Fin nDelta → ℝ) → (Fin nY → ℝ) →
      ((Fin nDelta → ℂ) → (Fin nY → ℂ) → ℂ) → ℝ → Prop
  | 0, nY, _, yRadius, F, M =>
      CMP116Eq214CauchyBoundaryBound nY yRadius (F Fin.elim0) M
  | nDelta + 1, nY, deltaRadius, yRadius, F, M =>
      ∀ s ∈ Set.uIoc (0 : ℝ) 1,
        ∀ z ∈ Metric.sphere (s : ℂ) (deltaRadius 0),
          CMP116Eq214NestedCauchyBoundaryBound nDelta nY
            (fun i => deltaRadius i.succ) yRadius
            (fun sigmaTail tau => F (Fin.cons z sigmaTail) tau) M

/-- Quantitative two-family estimate in the exact nesting order of (2.14). -/
theorem norm_cmp116Eq214NestedCauchyFamily_le_rate
    (nDelta nY : ℕ)
    (deltaRadius : Fin nDelta → ℝ) (yRadius : Fin nY → ℝ)
    (F : (Fin nDelta → ℂ) → (Fin nY → ℂ) → ℂ) (M : ℝ)
    (hDelta : ∀ i, 0 < deltaRadius i)
    (hY : ∀ i, 0 < yRadius i)
    (hF : CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      deltaRadius yRadius F M) :
    ‖cmp116Eq214CauchyFamily nDelta deltaRadius fun sigma =>
        cmp116Eq214CauchyFamily nY yRadius (F sigma)‖ ≤
      cmp116Eq214CauchyRate nDelta deltaRadius
        (cmp116Eq214CauchyRate nY yRadius M) := by
  induction nDelta with
  | zero =>
      simpa [cmp116Eq214CauchyFamily, cmp116Eq214CauchyRate,
        CMP116Eq214NestedCauchyBoundaryBound] using
        norm_cmp116Eq214CauchyFamily_le_rate nY yRadius (F Fin.elim0) M hY hF
  | succ nDelta ih =>
      rw [cmp116Eq214CauchyFamily_succ]
      apply norm_cmp116Eq214CauchyStep_le_div (hDelta 0)
      intro s hs z hz
      apply ih
      · intro i
        exact hDelta i.succ
      · exact hF s hs z hz

/-- Direct (2.14) consequence: a uniform joint contour bound on the nested
Gaussian integrand produces an explicit majorant for the literal physical
term. -/
theorem CMP116Eq214AnalyticData.norm_term_le_cauchyRate
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (ψ : Ψ) (φ : Φ) (M : ℝ)
    (hDelta : ∀ i, 0 < A.deltaRadius i)
    (hY : ∀ i, 0 < A.yRadius i)
    (hbound : CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      A.deltaRadius A.yRadius
      (fun sigma tau => A.analyticIntegrand Y0 P sigma tau ψ φ) M) :
    ‖A.term Y0 P ψ φ‖ ≤
      cmp116Eq214CauchyRate nDelta A.deltaRadius
        (cmp116Eq214CauchyRate nY A.yRadius M) := by
  exact norm_cmp116Eq214NestedCauchyFamily_le_rate
    nDelta nY A.deltaRadius A.yRadius
    (fun sigma tau => A.analyticIntegrand Y0 P sigma tau ψ φ)
    M hDelta hY hbound

end YangMills.RG
