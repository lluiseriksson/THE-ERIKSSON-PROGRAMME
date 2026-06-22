/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Schur-Catalan scalar budget closure

This module isolates the source-independent scalar bookkeeping behind the
spectral-local P4 route: a positive base quadratic form remains coercive after
subtracting finitely many multiscale defects, provided the total defect budget
is smaller than the base coercivity.

The optional Schur-Catalan budget

`(1 - sqrt (1 - 4 * M^2 * epsilon)) / (2 * M)`

is only a scalar envelope.  This file does not prove that the Yang--Mills
gauge-fixed Hessian, Schur complements, propagator localization, R-operation,
or raw activities satisfy such an envelope.  Those are the genuine P4 source
obligations.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

/-- Scalar Schur-Catalan self-energy envelope.  It is meaningful in the usual
smallness regime `0 <= 4 * M^2 * epsilon < 1` and `0 < M`, but the definition is
kept total so it can be used as a plain budget term in later finite estimates. -/
noncomputable def schurCatalanBudget (M epsilon : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * M ^ 2 * epsilon)) / (2 * M)

/-- Finite coercivity bookkeeping: if the base form dominates
`cBase * q v` and every selected defect is bounded by `budget i * q v`, then
the base minus the selected defects dominates the remaining scalar budget. -/
theorem quadraticBudget_sub_finset_le
    {ι E : Type*} [DecidableEq ι]
    (q : E → ℝ) (Qbase : E → ℝ) (defect : ι → E → ℝ)
    (budget : ι → ℝ) (s : Finset ι) {cBase : ℝ}
    (hbase : ∀ v, cBase * q v ≤ Qbase v)
    (hdefect : ∀ i, i ∈ s → ∀ v, defect i v ≤ budget i * q v) :
    ∀ v,
      (cBase - ∑ i ∈ s, budget i) * q v ≤
        Qbase v - ∑ i ∈ s, defect i v := by
  intro v
  have hsum :
      (∑ i ∈ s, defect i v) ≤
        ∑ i ∈ s, budget i * q v :=
    Finset.sum_le_sum (fun i hi => hdefect i hi v)
  have hfactor :
      (∑ i ∈ s, budget i * q v) =
        (∑ i ∈ s, budget i) * q v := by
    rw [Finset.sum_mul]
  have hsum' :
      (∑ i ∈ s, defect i v) ≤
        (∑ i ∈ s, budget i) * q v := by
    exact hsum.trans_eq hfactor
  calc
    (cBase - ∑ i ∈ s, budget i) * q v
        = cBase * q v - (∑ i ∈ s, budget i) * q v := by ring
    _ ≤ Qbase v - ∑ i ∈ s, defect i v := by
        linarith [hbase v, hsum']

/-- Strict finite coercivity closure: if the selected budget is strictly below
the base coercivity and `q v` is positive, then the base form minus defects is
strictly positive at `v`. -/
theorem quadraticBudget_sub_finset_pos
    {ι E : Type*} [DecidableEq ι]
    (q : E → ℝ) (Qbase : E → ℝ) (defect : ι → E → ℝ)
    (budget : ι → ℝ) (s : Finset ι) {cBase : ℝ}
    (hbase : ∀ v, cBase * q v ≤ Qbase v)
    (hdefect : ∀ i, i ∈ s → ∀ v, defect i v ≤ budget i * q v)
    (hbudget : (∑ i ∈ s, budget i) < cBase) :
    ∀ v, 0 < q v →
      0 < Qbase v - ∑ i ∈ s, defect i v := by
  intro v hqpos
  have hlower :=
    quadraticBudget_sub_finset_le q Qbase defect budget s hbase hdefect v
  have hleft : 0 < (cBase - ∑ i ∈ s, budget i) * q v := by
    exact mul_pos (sub_pos.mpr hbudget) hqpos
  exact hleft.trans_le hlower

/-- Schur-Catalan lower-bound form of the finite closure.  The theorem is just
the scalar budget bookkeeping after choosing the Catalan envelope for each
scale. -/
theorem schurCatalan_lower_bound_of_finset_budget
    {ι E : Type*} [DecidableEq ι]
    (q : E → ℝ) (Qbase : E → ℝ) (defect : ι → E → ℝ)
    (M epsilon : ι → ℝ) (s : Finset ι) {cBase : ℝ}
    (hbase : ∀ v, cBase * q v ≤ Qbase v)
    (hdefect : ∀ i, i ∈ s → ∀ v,
      defect i v ≤ schurCatalanBudget (M i) (epsilon i) * q v) :
    ∀ v,
      (cBase - ∑ i ∈ s, schurCatalanBudget (M i) (epsilon i)) * q v ≤
        Qbase v - ∑ i ∈ s, defect i v := by
  exact quadraticBudget_sub_finset_le q Qbase defect
    (fun i => schurCatalanBudget (M i) (epsilon i)) s hbase hdefect

/-- Schur-Catalan strict finite coercivity closure.  This is the finite-scale
version of the abstract principle "base positivity beats the accumulated
Schur-Catalan self-energy budget". -/
theorem schurCatalan_coercive_of_finset_budget
    {ι E : Type*} [DecidableEq ι]
    (q : E → ℝ) (Qbase : E → ℝ) (defect : ι → E → ℝ)
    (M epsilon : ι → ℝ) (s : Finset ι) {cBase : ℝ}
    (hbase : ∀ v, cBase * q v ≤ Qbase v)
    (hdefect : ∀ i, i ∈ s → ∀ v,
      defect i v ≤ schurCatalanBudget (M i) (epsilon i) * q v)
    (hbudget :
      (∑ i ∈ s, schurCatalanBudget (M i) (epsilon i)) < cBase) :
    ∀ v, 0 < q v →
      0 < Qbase v - ∑ i ∈ s, defect i v := by
  exact quadraticBudget_sub_finset_pos q Qbase defect
    (fun i => schurCatalanBudget (M i) (epsilon i)) s
    hbase hdefect hbudget

end YangMills.RG
