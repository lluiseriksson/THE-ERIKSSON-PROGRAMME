/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Lemma3

/-!
# CMP116 equation (2.29) summability interface

Balaban CMP 116, page 18, equation (2.29), bounds the first resummation over
families `D` by

`sum_D prod_{Y in D} alpha_6 * exp (-delta * kappa * d_k(Y)) <= 1`.

This module records that exact source shape and proves the local finite-sum
consumer used by the Lemma 3 resummation route: if a D-indexed term is bounded
by a nonnegative base factor times the (2.29) product, then the sum over `D`
is bounded by the base factor.

Honest scope: the predicate `CMP116Eq229Summability` is still a source
summability input.  This file does not prove Balaban's "for K sufficiently
large and alpha_6 sufficiently small" assertion, does not prove equations
(2.27), (2.30), (2.32), (2.34), (2.36), (2.37), and does not derive the final
Lemma 3 budget.
-/

namespace YangMills.RG

open scoped BigOperators

/-- The source weight in CMP116 equation (2.29):
`alpha_6 * exp (-delta * kappa * d_k(Y))`. -/
noncomputable def cmp116Eq229Weight
    {ιY : Type*}
    (alpha6 delta kappa : ℝ)
    (metric : ιY → ℕ)
    (Y : ιY) : ℝ :=
  alpha6 * Real.exp (-(delta * kappa * (metric Y : ℝ)))

/-- The CMP116 equation (2.29) source summability shape.

The parameter `σ` is the fixed source component/context, corresponding to the
fixed `Y_0` in the proof around (2.29). -/
def CMP116Eq229Summability
    {σ ιD ιY : Type*}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ) : Prop :=
  ∀ Y0,
    Finset.sum (DIndex Y0)
        (fun D =>
          Finset.prod (DParts Y0 D)
            (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) ≤
      1

/-- The CMP116 (2.29) weight is nonnegative when `alpha_6` is nonnegative. -/
theorem cmp116Eq229Weight_nonneg
    {ιY : Type*}
    {alpha6 delta kappa : ℝ}
    {metric : ιY → ℕ}
    (halpha6 : 0 ≤ alpha6)
    (Y : ιY) :
    0 ≤ cmp116Eq229Weight alpha6 delta kappa metric Y := by
  exact mul_nonneg halpha6 (Real.exp_nonneg _)

/-- First-stage D-sum consumer for CMP116 equation (2.29).

If every term in the D-sum is bounded by a nonnegative base factor times the
product appearing in (2.29), then the whole D-sum is bounded by the base factor.
This proves only the local resummation step attached to (2.29), not the final
Lemma 3 estimate. -/
theorem cmp116_DStage_sum_le_of_eq229
    {σ ιD ιY τ : Type*}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (base : σ → τ → ℝ)
    (term : σ → ιD → τ → ℝ)
    (hEq229 :
      CMP116Eq229Summability
        DIndex DParts alpha6 delta kappa metric)
    (hbase_nonneg : ∀ Y0 t, 0 ≤ base Y0 t)
    (hterm :
      ∀ Y0 D, D ∈ DIndex Y0 → ∀ t,
        term Y0 D t ≤
          base Y0 t *
            Finset.prod (DParts Y0 D)
              (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) :
    ∀ Y0 t,
      Finset.sum (DIndex Y0) (fun D => term Y0 D t) ≤
        base Y0 t := by
  intro Y0 t
  calc
    Finset.sum (DIndex Y0) (fun D => term Y0 D t)
        ≤ Finset.sum (DIndex Y0)
            (fun D =>
              base Y0 t *
                Finset.prod (DParts Y0 D)
                  (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) := by
      exact Finset.sum_le_sum (fun D hD => hterm Y0 D hD t)
    _ =
        base Y0 t *
          Finset.sum (DIndex Y0)
            (fun D =>
              Finset.prod (DParts Y0 D)
                (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) := by
      simp [Finset.mul_sum]
    _ ≤ base Y0 t * 1 := by
      exact mul_le_mul_of_nonneg_left (hEq229 Y0) (hbase_nonneg Y0 t)
    _ = base Y0 t := by ring

end YangMills.RG
