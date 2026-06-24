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

Honest scope: the P-stage source budget is now named and mapped to the
normalized P residual predicate; the `Z0` and `Z0'` stages, the analytic
constant hierarchy, and the model-specific identification of `H(Z)` remain
unassigned.  This module only proves the finite residual resummation algebra
needed before applying equation (2.29).
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

/-- The source-shaped `P`-stage estimate in the CMP116 Lemma-3 resummation,
before applying the corresponding scalar smallness restriction.

CMP116, Lemma-3 proof on printed pages 18--20: the P/residual resummation step
uses the geometric inequality (2.30) as an input and later applies the displayed
restriction `2 (L+2)^4 O(1) epsilon2 exp(5 kappa) <= 1`.  The constant
`pEntropyConstant` names the source's stage-specific `O(1)` majorant.  This
predicate records only the source-shaped finite bound; it does not construct
the source `P` family, identify `pWeight`, or prove the scalar restriction. -/
def CMP116PStageSourceBound
    {σ ιD ιP : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (pWeight : σ → ιD → ιP → ℝ)
    (blockScale : ℕ)
    (pEntropyConstant epsilon2 kappa : ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    Finset.sum (PIndex Z D) (fun P => pWeight Z D P) ≤
      2 * (((blockScale : ℝ) + 2) ^ 4) *
        pEntropyConstant * epsilon2 * Real.exp (5 * kappa)

/-- The CMP116 P-stage source estimate, together with its explicit scalar
smallness restriction, implies the source-neutral normalized P-stage predicate
used by the finite residual resummation. -/
theorem cmp116PResidualSummability_of_pStageSourceBound
    {σ ιD ιP : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (pWeight : σ → ιD → ιP → ℝ)
    (blockScale : ℕ)
    (pEntropyConstant epsilon2 kappa : ℝ)
    (hsource :
      CMP116PStageSourceBound
        DIndex PIndex pWeight
        blockScale pEntropyConstant epsilon2 kappa)
    (hsmall :
      2 * (((blockScale : ℝ) + 2) ^ 4) *
          pEntropyConstant * epsilon2 * Real.exp (5 * kappa) ≤ 1) :
    CMP116PResidualSummability DIndex PIndex pWeight := by
  intro Z D hD
  exact (hsource Z D hD).trans hsmall

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

/-- Normalized residual `Z0/Z0'` summability, plus a pointwise
factorization, implies a fixed-`P` post-residual budget.

This is the inner version of `cmp116H_postD_sum_le_of_residualStages`.  It
keeps the `P`-stage budget separate, matching the source order after the
equation-(2.29) `D` summation without asserting any analytic source estimate. -/
theorem cmp116H_postP_sum_le_of_residualStages
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (base : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hbase_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ base Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                (base Z D P * z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') :
    ∀ Z D, D ∈ R.DIndex Z →
      ∀ P, P ∈ R.PIndex Z D →
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0')) ≤
          base Z D P := by
  intro Z D hD P hP
  have hZ0PrimeStage :
      ∀ Z0, Z0 ∈ R.Z0Index Z D P →
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0') ≤
          base Z D P * z0Weight Z D P Z0 := by
    intro Z0 hZ0
    have hprefix_nonneg :
        0 ≤ base Z D P * z0Weight Z D P Z0 := by
      exact
        mul_nonneg
          (hbase_nonneg Z D hD P hP)
          (hz0Weight_nonneg Z D hD P hP Z0 hZ0)
    calc
      Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')
          ≤
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          (base Z D P * z0Weight Z D P Z0) *
            z0PrimeWeight Z D P Z0 Z0') := by
          exact Finset.sum_le_sum
            (fun Z0' hZ0' => hfactor Z D hD P hP Z0 hZ0 Z0' hZ0')
      _ =
        (base Z D P * z0Weight Z D P Z0) *
          Finset.sum (R.Z0PrimeIndex Z D P Z0)
            (fun Z0' => z0PrimeWeight Z D P Z0 Z0') := by
          simp [Finset.mul_sum]
      _ ≤
        (base Z D P * z0Weight Z D P Z0) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (hZ0PrimeSum Z D hD P hP Z0 hZ0) hprefix_nonneg
      _ = base Z D P * z0Weight Z D P Z0 := by
          ring
  calc
    Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0'))
        ≤
      Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        base Z D P * z0Weight Z D P Z0) := by
        exact Finset.sum_le_sum (fun Z0 hZ0 => hZ0PrimeStage Z0 hZ0)
    _ =
      base Z D P *
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          z0Weight Z D P Z0) := by
        simp [Finset.mul_sum]
    _ ≤ base Z D P * 1 := by
        exact mul_le_mul_of_nonneg_left
          (hZ0sum Z D hD P hP) (hbase_nonneg Z D hD P hP)
    _ = base Z D P := by
        ring

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

/-- A source-shaped CMP116 P-stage bound plus its explicit scalar smallness
restriction feeds the normalized residual-stage post-`D` bridge.

This theorem only replaces the source-neutral `CMP116PResidualSummability`
hypothesis by the already named P-stage source-bound interface.  The `Z0` and
`Z0'` residual stages, nonnegativity, and pointwise factorization remain
explicit hypotheses. -/
theorem cmp116H_postD_sum_le_of_pStageSourceBound_residualStages
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (base : σ → ιD → ℝ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (blockScale : ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℝ)
    (hPsource :
      CMP116PStageSourceBound
        R.DIndex R.PIndex pWeight
        blockScale pEntropyConstant epsilon2 pStageKappa)
    (hPsmall :
      2 * (((blockScale : ℝ) + 2) ^ 4) *
          pEntropyConstant * epsilon2 * Real.exp (5 * pStageKappa) ≤ 1)
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
  exact
    cmp116H_postD_sum_le_of_residualStages
      R base pWeight z0Weight z0PrimeWeight
      (cmp116PResidualSummability_of_pStageSourceBound
        R.DIndex R.PIndex pWeight
        blockScale pEntropyConstant epsilon2 pStageKappa
        hPsource hPsmall)
      hZ0sum hZ0PrimeSum
      hbase_nonneg hpWeight_nonneg hz0Weight_nonneg hfactor

/-- A P-stage budget plus normalized fixed-`P` residual stages implies the
post-`D` residual budget required by the equation-(2.29) consumer.

This is finite summation bookkeeping only.  It does not prove the P-stage
budget, the `Z0/Z0'` residual estimates, or the CMP116 source constants. -/
theorem cmp116H_postD_sum_le_of_pStageResidualStages
    {σ ιD ιP ιZ0 ιZ0' ιY Ψ Φ : Type*}
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hPStage :
      CMP116PStageSummability
        R.DIndex R.PIndex pWeight
        (fun Z D =>
          Finset.prod (DParts Z D)
            (cmp116Eq229Weight
              alpha6 hp.delta hp.kappa (eq229Metric Z))))
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                ((((hp.C3 * hp.epsilon1) *
                    balabanCMP116Lemma3Weight
                      hp.blockScale hp.delta hp.kappa sourceMetric Z) *
                    pWeight Z D P) *
                  z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') :
    ∀ Z D, D ∈ R.DIndex Z →
      Finset.sum (R.PIndex Z D) (fun P =>
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0'))) ≤
        ((hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z) *
          Finset.prod (DParts Z D)
            (cmp116Eq229Weight
              alpha6 hp.delta hp.kappa (eq229Metric Z)) := by
  let postPBase : σ → ιD → ιP → ℝ := fun Z D P =>
    ((hp.C3 * hp.epsilon1) *
      balabanCMP116Lemma3Weight
        hp.blockScale hp.delta hp.kappa sourceMetric Z) *
      pWeight Z D P
  have hpostPBase_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ postPBase Z D P := by
    intro Z D hD P hP
    exact
      mul_nonneg
        (mul_nonneg hp.amplitude_nonneg
          (balabanCMP116Lemma3Weight_nonneg
            hp.blockScale hp.delta hp.kappa sourceMetric Z))
        (hpWeight_nonneg Z D hD P hP)
  have hpostP :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          Finset.sum (R.Z0Index Z D P) (fun Z0 =>
            Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
              R.termWeight Z D P Z0 Z0')) ≤
            postPBase Z D P :=
    cmp116H_postP_sum_le_of_residualStages
      R postPBase z0Weight z0PrimeWeight
      hZ0sum hZ0PrimeSum
      hpostPBase_nonneg
      hz0Weight_nonneg
      (fun Z D hD P hP Z0 hZ0 Z0' hZ0' => by
        simpa [postPBase, mul_assoc] using
          hfactor Z D hD P hP Z0 hZ0 Z0' hZ0')
  simpa [postPBase] using
    cmp116H_postDSum_le_of_pStage
      hp R sourceMetric DParts alpha6 eq229Metric
      pWeight hPStage hpostP

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

/-- Equation (2.29), a source-shaped P-stage bound plus scalar smallness, and
normalized `Z0/Z0'` residual stages give the finite CMP116 `H` term-weight
budget.

The P-stage is the only premise discharged by this wrapper.  The equation
(2.29), later residual stages, nonnegativity, and pointwise source
factorization are still carried explicitly. -/
theorem cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages
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
    (blockScale : ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℝ)
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hPsource :
      CMP116PStageSourceBound
        R.DIndex R.PIndex pWeight
        blockScale pEntropyConstant epsilon2 pStageKappa)
    (hPsmall :
      2 * (((blockScale : ℝ) + 2) ^ 4) *
          pEntropyConstant * epsilon2 * Real.exp (5 * pStageKappa) ≤ 1)
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
  exact
    cmp116H_termWeightSum_le_of_eq229_of_residualStages
      hp R sourceMetric DParts alpha6 eq229Metric
      pWeight z0Weight z0PrimeWeight
      hEq229
      (cmp116PResidualSummability_of_pStageSourceBound
        R.DIndex R.PIndex pWeight
        blockScale pEntropyConstant epsilon2 pStageKappa
        hPsource hPsmall)
      hZ0sum hZ0PrimeSum
      halpha6 hpWeight_nonneg hz0Weight_nonneg hfactor

/-- Equation (2.29), the source-shaped CMP116 P-stage bound, and normalized
`Z0/Z0'` residual stages feed the theorem-backed CMP116 Lemma 3 activity
estimate.

This is the activity-level wrapper for
`cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages`; it
does not identify the physical activity, termwise complex bound, or remaining
residual estimates with source statements. -/
theorem cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages
    {σ ιD ιP ιZ0 ιZ0' ιY : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : CMP116Lemma3Parameters)
    (R :
      CMP116HResummation σ ιD ιP ιZ0 ιZ0'
        (PhysicalGaugeField dPhys N Nc)
        (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : σ → ℕ)
    (physicalActivity : σ → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (blockScale : ℕ)
    (pEntropyConstant epsilon2 pStageKappa : ℝ)
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hPsource :
      CMP116PStageSourceBound
        R.DIndex R.PIndex pWeight
        blockScale pEntropyConstant epsilon2 pStageKappa)
    (hPsmall :
      2 * (((blockScale : ℝ) + 2) ^ 4) *
          pEntropyConstant * epsilon2 * Real.exp (5 * pStageKappa) ≤ 1)
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hglobal :
      ∀ Z ψ φ,
        (physicalActivity Z).globalEval ψ φ =
          balabanCMP116H R Z ψ φ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
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
    CMP116Lemma3ActivityEstimate
      physicalActivity sourceMetric hp.blockScale
      hp.C3 hp.epsilon1 hp.delta hp.kappa := by
  exact
    cmp116Lemma3ActivityEstimate_of_resummation
      hp R sourceMetric physicalActivity
      hglobal hterm
      (cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages
        hp R sourceMetric DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        blockScale pEntropyConstant epsilon2 pStageKappa
        hEq229 hPsource hPsmall hZ0sum hZ0PrimeSum
        halpha6 hpWeight_nonneg hz0Weight_nonneg hfactor)

/-- Equation (2.29), a P-stage budget, and normalized fixed-`P`
`Z0/Z0'` residual stages give the finite CMP116 `H` term-weight budget.

This variant is useful when the P-stage has already been bounded by the
equation-(2.29) product budget, while the later residual stages remain
separately normalized. -/
theorem cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages
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
    (hPStage :
      CMP116PStageSummability
        R.DIndex R.PIndex pWeight
        (fun Z D =>
          Finset.prod (DParts Z D)
            (cmp116Eq229Weight
              alpha6 hp.delta hp.kappa (eq229Metric Z))))
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                ((((hp.C3 * hp.epsilon1) *
                    balabanCMP116Lemma3Weight
                      hp.blockScale hp.delta hp.kappa sourceMetric Z) *
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
  exact
    cmp116H_termWeightSum_le_of_eq229
      hp R sourceMetric DParts alpha6 eq229Metric hEq229
      (cmp116H_postD_sum_le_of_pStageResidualStages
        hp R sourceMetric DParts alpha6 eq229Metric
        pWeight z0Weight z0PrimeWeight
        hPStage hZ0sum hZ0PrimeSum
        hpWeight_nonneg hz0Weight_nonneg hfactor)

/-- Eq. (2.29), an explicit P-stage budget, and normalized fixed-`P`
residual stages feed the theorem-backed CMP116 Lemma 3 activity estimate.

The theorem keeps the activity identification, complex termwise estimate,
P-stage budget, and `Z0/Z0'` residual estimates as explicit hypotheses. -/
theorem cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages
    {σ ιD ιP ιZ0 ιZ0' ιY : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    {dPhys N Nc : ℕ} [NeZero N]
    (hp : CMP116Lemma3Parameters)
    (R :
      CMP116HResummation σ ιD ιP ιZ0 ιZ0'
        (PhysicalGaugeField dPhys N Nc)
        (PhysicalGaugeField dPhys N Nc))
    (sourceMetric : σ → ℕ)
    (physicalActivity : σ → PhysicalGaugeLocalActivity dPhys N Nc)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hPStage :
      CMP116PStageSummability
        R.DIndex R.PIndex pWeight
        (fun Z D =>
          Finset.prod (DParts Z D)
            (cmp116Eq229Weight
              alpha6 hp.delta hp.kappa (eq229Metric Z))))
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hglobal :
      ∀ Z ψ φ,
        (physicalActivity Z).globalEval ψ φ =
          balabanCMP116H R Z ψ φ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            0 ≤ z0Weight Z D P Z0)
    (hfactor :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          ∀ Z0, Z0 ∈ R.Z0Index Z D P →
            ∀ Z0', Z0' ∈ R.Z0PrimeIndex Z D P Z0 →
              R.termWeight Z D P Z0 Z0' ≤
                ((((hp.C3 * hp.epsilon1) *
                    balabanCMP116Lemma3Weight
                      hp.blockScale hp.delta hp.kappa sourceMetric Z) *
                    pWeight Z D P) *
                  z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') :
    CMP116Lemma3ActivityEstimate
      physicalActivity sourceMetric hp.blockScale
      hp.C3 hp.epsilon1 hp.delta hp.kappa :=
  cmp116Lemma3ActivityEstimate_of_resummation
    hp R sourceMetric physicalActivity
    hglobal hterm
    (cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages
      hp R sourceMetric DParts alpha6 eq229Metric
      pWeight z0Weight z0PrimeWeight
      hEq229 hPStage hZ0sum hZ0PrimeSum
      hpWeight_nonneg hz0Weight_nonneg hfactor)

end YangMills.RG
