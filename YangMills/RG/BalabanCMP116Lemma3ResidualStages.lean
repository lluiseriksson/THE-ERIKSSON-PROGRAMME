/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229

/-!
# CMP116 residual-stage resummation interface

This module separates the residual `P`, `Z0`, and `Z0'` source summations from
the equation-(2.29) `D`-summability consumer.

The predicates below are source-neutral normalized summability statements.  The
main theorem proves that these three normalized residual stages, together with
a pointwise factorization of the term weights, imply the post-`D` residual
budget consumed by `cmp116H_termWeightSum_le_of_eq229`.

Honest scope: this file does not assign the residual predicates to CMP116
equations (2.27), (2.30), (2.32), (2.34), (2.36), or (2.37), does not prove
the analytic constants, and does not identify `H(Z)` with a model-specific
activity.  It only proves the finite residual resummation algebra needed before
applying equation (2.29).
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source-neutral normalized residual summability for the `P` stage after a
fixed `D`. -/
def CMP116PResidualSummability
    {σ ιD ιP : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (pWeight : σ → ιD → ιP → ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    Finset.sum (PIndex Z D) (fun P => pWeight Z D P) ≤ 1

/-- Source-neutral normalized residual summability for the `Z0` stage after a
fixed `D` and `P`. -/
def CMP116Z0ResidualSummability
    {σ ιD ιP ιZ0 : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (Z0Index : σ → ιD → ιP → Finset ιZ0)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    ∀ P, P ∈ PIndex Z D →
      Finset.sum (Z0Index Z D P) (fun Z0 => z0Weight Z D P Z0) ≤ 1

/-- Source-neutral normalized residual summability for the `Z0'` stage after a
fixed `D`, `P`, and `Z0`. -/
def CMP116Z0PrimeResidualSummability
    {σ ιD ιP ιZ0 ιZ0' : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (Z0Index : σ → ιD → ιP → Finset ιZ0)
    (Z0PrimeIndex : σ → ιD → ιP → ιZ0 → Finset ιZ0')
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    ∀ P, P ∈ PIndex Z D →
      ∀ Z0, Z0 ∈ Z0Index Z D P →
        Finset.sum (Z0PrimeIndex Z D P Z0)
          (fun Z0' => z0PrimeWeight Z D P Z0 Z0') ≤ 1

/-- Normalized residual `P/Z0/Z0'` summability, plus a pointwise factorization,
implies the post-`D` residual budget required by the equation-(2.29) consumer.

Nonnegativity is required only for the factors that are multiplied into an
already normalized finite sum.  No nonnegativity hypothesis on the final
`Z0'` weight is needed. -/
theorem cmp116H_postD_sum_le_of_residualStages
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (base : σ → ιD → ℝ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hPsum :
      CMP116PResidualSummability
        R.DIndex R.PIndex pWeight)
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hbase_nonneg :
      ∀ Z D, D ∈ R.DIndex Z → 0 ≤ base Z D)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P → 0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                ((base Z D * pWeight Z D P) *
                    z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') :
    ∀ Z D, D ∈ R.DIndex Z →
      Finset.sum (R.PIndex Z D) (fun P =>
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0'))) ≤
        base Z D := by
  intro Z D hD
  have hZ0PrimeStage :
      ∀ P, P ∈ R.PIndex Z D →
        ∀ Z0, Z0 ∈ R.Z0Index Z D P →
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0') ≤
            (base Z D * pWeight Z D P) * z0Weight Z D P Z0 := by
    intro P hP Z0 hZ0
    have hprefix_nonneg :
        0 ≤ (base Z D * pWeight Z D P) * z0Weight Z D P Z0 := by
      exact
        mul_nonneg
          (mul_nonneg (hbase_nonneg Z D hD)
            (hpWeight_nonneg Z D hD P hP))
          (hz0Weight_nonneg Z D hD P hP Z0 hZ0)
    calc
      Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')
          ≤
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          ((base Z D * pWeight Z D P) * z0Weight Z D P Z0) *
            z0PrimeWeight Z D P Z0 Z0') := by
          exact Finset.sum_le_sum
            (fun Z0' hZ0' => hfactor Z D hD P hP Z0 hZ0 Z0' hZ0')
      _ =
        ((base Z D * pWeight Z D P) * z0Weight Z D P Z0) *
          Finset.sum (R.Z0PrimeIndex Z D P Z0)
            (fun Z0' => z0PrimeWeight Z D P Z0 Z0') := by
          simp [Finset.mul_sum]
      _ ≤
        ((base Z D * pWeight Z D P) * z0Weight Z D P Z0) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (hZ0PrimeSum Z D hD P hP Z0 hZ0) hprefix_nonneg
      _ = (base Z D * pWeight Z D P) * z0Weight Z D P Z0 := by
          ring
  have hZ0Stage :
      ∀ P, P ∈ R.PIndex Z D →
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0')) ≤
          base Z D * pWeight Z D P := by
    intro P hP
    have hprefix_nonneg : 0 ≤ base Z D * pWeight Z D P := by
      exact mul_nonneg (hbase_nonneg Z D hD)
        (hpWeight_nonneg Z D hD P hP)
    calc
      Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0'))
          ≤
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          (base Z D * pWeight Z D P) * z0Weight Z D P Z0) := by
          exact Finset.sum_le_sum
            (fun Z0 hZ0 => hZ0PrimeStage P hP Z0 hZ0)
      _ =
        (base Z D * pWeight Z D P) *
          Finset.sum (R.Z0Index Z D P) (fun Z0 =>
            z0Weight Z D P Z0) := by
          simp [Finset.mul_sum]
      _ ≤ (base Z D * pWeight Z D P) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (hZ0sum Z D hD P hP) hprefix_nonneg
      _ = base Z D * pWeight Z D P := by
          ring
  calc
    Finset.sum (R.PIndex Z D) (fun P =>
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0')))
        ≤
      Finset.sum (R.PIndex Z D) (fun P =>
        base Z D * pWeight Z D P) := by
        exact Finset.sum_le_sum (fun P hP => hZ0Stage P hP)
    _ =
      base Z D *
        Finset.sum (R.PIndex Z D) (fun P => pWeight Z D P) := by
        simp [Finset.mul_sum]
    _ ≤ base Z D * 1 := by
        exact mul_le_mul_of_nonneg_left (hPsum Z D hD) (hbase_nonneg Z D hD)
    _ = base Z D := by
        ring

/-- Equation (2.29) plus source-neutral normalized residual stages gives the
finite CMP116 `H` term-weight budget.

This is a thin composition theorem: the residual-stage theorem produces the
post-`D` hypothesis expected by `cmp116H_termWeightSum_le_of_eq229`, whose
`D`-summability step is exactly equation (2.29). -/
theorem cmp116H_termWeightSum_le_of_eq229_of_residualStages
    {σ ιD ιP ιZ0 ιZ0' ιY Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hPsum :
      CMP116PResidualSummability
        R.DIndex R.PIndex pWeight)
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (halpha6 : 0 ≤ alpha6)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P → 0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                (((((hp.C3 * hp.epsilon1) *
                    balabanCMP116Lemma3Weight
                      hp.blockScale hp.delta hp.kappa sourceMetric Z) *
                    Finset.prod (DParts Z D)
                      (cmp116Eq229Weight
                        alpha6 hp.delta hp.kappa (eq229Metric Z))) *
                    pWeight Z D P) *
                    z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') :
    ∀ Z,
      Finset.sum (cmp116HIndexFinset R Z)
        (fun x =>
          R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z := by
  let postDBase : σ → ιD → ℝ := fun Z D =>
    ((hp.C3 * hp.epsilon1) *
        balabanCMP116Lemma3Weight
          hp.blockScale hp.delta hp.kappa sourceMetric Z) *
      Finset.prod (DParts Z D)
        (cmp116Eq229Weight alpha6 hp.delta hp.kappa (eq229Metric Z))
  have hpostDBase_nonneg :
      ∀ Z D, D ∈ R.DIndex Z → 0 ≤ postDBase Z D := by
    intro Z D _
    exact
      mul_nonneg
        (mul_nonneg hp.amplitude_nonneg
          (balabanCMP116Lemma3Weight_nonneg
            hp.blockScale hp.delta hp.kappa sourceMetric Z))
        (Finset.prod_nonneg
          (fun Y _ =>
            cmp116Eq229Weight_nonneg
              (metric := eq229Metric Z) halpha6 Y))
  have hfactor' :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                ((postDBase Z D * pWeight Z D P) *
                    z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0' := by
    intro Z D hD P hP Z0 hZ0 Z0' hZ0'
    simpa [postDBase, mul_assoc] using hfactor Z D hD P hP Z0 hZ0 Z0' hZ0'
  have hpostD :
      ∀ Z D, D ∈ R.DIndex Z →
        Finset.sum (R.PIndex Z D) (fun P =>
          Finset.sum (R.Z0Index Z D P) (fun Z0 =>
            Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
              R.termWeight Z D P Z0 Z0'))) ≤
          postDBase Z D :=
    cmp116H_postD_sum_le_of_residualStages
      R postDBase pWeight z0Weight z0PrimeWeight
      hPsum hZ0sum hZ0PrimeSum
      hpostDBase_nonneg hpWeight_nonneg hz0Weight_nonneg hfactor'
  simpa [postDBase] using
    cmp116H_termWeightSum_le_of_eq229
      hp R sourceMetric DParts alpha6 eq229Metric hEq229 hpostD

end YangMills.RG
