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
budget consumed by `cmp116H_termWeightSum_le_of_eq229`.  The module also exposes
a direct combined post-`P` residual budget for source statements that do not
faithfully split into separate normalized `Z0` and `Z0'` estimates.

Honest scope: the P-stage source budget is now named and mapped to the
normalized P residual predicate; the `Z0` source-shaped budget is named and
mapped to its normalized residual predicate; the `Z0'` stage, the analytic
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

/-- Canonical P-stage weight obtained by multiplying a normalized residual
P-weight by the fixed-`D` Eq. (2.29) product. -/
noncomputable def cmp116Eq229WeightedPWeight
    {σ ιD ιP ιY : Type*}
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (pResidualWeight : σ → ιD → ιP → ℝ) :
    σ → ιD → ιP → ℝ :=
  fun Z D P =>
    cmp116Eq229Product DParts alpha6 delta kappa metric Z D *
      pResidualWeight Z D P

/-- The Eq. (2.29)-weighted P-weight is nonnegative when the Eq. (2.29)
weight and the normalized P-weight are nonnegative. -/
theorem cmp116Eq229WeightedPWeight_nonneg
    {σ ιD ιP ιY : Type*}
    {DParts : σ → ιD → Finset ιY}
    {alpha6 delta kappa : ℝ}
    {metric : σ → ιY → ℕ}
    {pResidualWeight : σ → ιD → ιP → ℝ}
    (halpha6 : 0 ≤ alpha6)
    (hpResidual_nonneg :
      ∀ Z D P, 0 ≤ pResidualWeight Z D P)
    (Z : σ) (D : ιD) (P : ιP) :
    0 ≤
      cmp116Eq229WeightedPWeight
        DParts alpha6 delta kappa metric pResidualWeight Z D P := by
  exact
    mul_nonneg
      (cmp116Eq229Product_nonneg
        (DParts := DParts) (metric := metric) halpha6 Z D)
      (hpResidual_nonneg Z D P)

/-- A normalized P-stage sum becomes the canonical CMP116 P-stage budget after
weighting by the Eq. (2.29) product.

This avoids replacing the product budget by an unrelated scalar smallness
bound.  It proves only finite-sum algebra; the source estimate for the
normalized P-weight remains an explicit hypothesis. -/
theorem cmp116PStageSummability_of_pResidualSummability_weighted
    {σ ιD ιP ιY : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (pResidualWeight : σ → ιD → ιP → ℝ)
    (hPResidual :
      CMP116PResidualSummability
        DIndex PIndex pResidualWeight)
    (halpha6 : 0 ≤ alpha6) :
    CMP116PStageSummability
      DIndex PIndex
      (cmp116Eq229WeightedPWeight
        DParts alpha6 delta kappa metric pResidualWeight)
      (cmp116Eq229Product DParts alpha6 delta kappa metric) := by
  intro Z D hD
  let B : ℝ :=
    cmp116Eq229Product DParts alpha6 delta kappa metric Z D
  have hB_nonneg : 0 ≤ B := by
    exact
      cmp116Eq229Product_nonneg
        (DParts := DParts) (metric := metric) halpha6 Z D
  calc
    Finset.sum (PIndex Z D)
        (fun P =>
          cmp116Eq229WeightedPWeight
            DParts alpha6 delta kappa metric pResidualWeight Z D P)
        =
      B * Finset.sum (PIndex Z D)
        (fun P => pResidualWeight Z D P) := by
          simp [cmp116Eq229WeightedPWeight, B, Finset.mul_sum]
    _ ≤ B * 1 := by
          exact
            mul_le_mul_of_nonneg_left
              (hPResidual Z D hD)
              hB_nonneg
    _ =
      cmp116Eq229Product DParts alpha6 delta kappa metric Z D := by
          simp [B]

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

/-- The source-shaped `Z0`-stage estimate in the CMP116 Lemma-3 resummation,
before applying the corresponding scalar smallness restriction.

CMP116, printed page 19 around equation (2.32): the `Z0` resummation produces
the stage scalar `(L+2)^4 O(1) epsilon2`.  The constant
`z0EntropyConstant` names the stage-specific `O(1)` majorant.

This predicate does not construct the source `Z0` family, identify `z0Weight`,
or prove the scalar restriction. -/
def CMP116Z0StageSourceBound
    {σ ιD ιP ιZ0 : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (Z0Index : σ → ιD → ιP → Finset ιZ0)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (blockScale : ℕ)
    (z0EntropyConstant epsilon2 : ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    ∀ P, P ∈ PIndex Z D →
      Finset.sum (Z0Index Z D P)
          (fun Z0 => z0Weight Z D P Z0) ≤
        (((blockScale : ℝ) + 2) ^ 4) *
          z0EntropyConstant * epsilon2

/-- The CMP116 `Z0`-stage source estimate, together with its explicit scalar
smallness restriction, implies the source-neutral normalized `Z0` residual
predicate. -/
theorem cmp116Z0ResidualSummability_of_z0StageSourceBound
    {σ ιD ιP ιZ0 : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (Z0Index : σ → ιD → ιP → Finset ιZ0)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (blockScale : ℕ)
    (z0EntropyConstant epsilon2 : ℝ)
    (hsource :
      CMP116Z0StageSourceBound
        DIndex PIndex Z0Index z0Weight
        blockScale z0EntropyConstant epsilon2)
    (hsmall :
      (((blockScale : ℝ) + 2) ^ 4) *
          z0EntropyConstant * epsilon2 ≤ 1) :
    CMP116Z0ResidualSummability
      DIndex PIndex Z0Index z0Weight := by
  intro Z D hD P hP
  exact (hsource Z D hD P hP).trans hsmall

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

/-- A source-side post-`P` residual budget for the combined `Z0/Z0'` finite sum.

This keeps the source-shaped amplitude and source weight separate from the
canonical CMP116 Lemma-3 base factor.  The adapter below records the explicit
majorization needed to feed such a source statement into the downstream
consumer `CMP116PostPResidualBound`. -/
def CMP116PostPResidualSourceBound
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (postPSourceWeight : σ → ℝ)
    (postPAmplitude : ℝ)
    (pWeight : σ → ιD → ιP → ℝ) : Prop :=
  ∀ Z D, D ∈ R.DIndex Z →
    ∀ P, P ∈ R.PIndex Z D →
      Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')) ≤
        (postPAmplitude * postPSourceWeight Z) *
          pWeight Z D P

/-- A direct post-`P` residual consumer budget for the combined `Z0/Z0'` finite
sum.

This is the source-safe final consumer boundary when the primary text supplies a
combined estimate for the last two resummations, or supplies them in an order
different from the repository's dependent `Z0 -> Z0'` indexing.  It avoids
pretending that the normalized `Z0` and `Z0'` predicates have already been
separately identified with source equations. -/
def CMP116PostPResidualBound
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (pWeight : σ → ιD → ιP → ℝ) : Prop :=
  ∀ Z D, D ∈ R.DIndex Z →
    ∀ P, P ∈ R.PIndex Z D →
      Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')) ≤
        ((hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z) *
          pWeight Z D P

/-- A source-shaped combined post-`P` residual estimate feeds the canonical
post-`P` consumer bound once its amplitude/weight is majorized by the CMP116
Lemma-3 base factor. -/
theorem cmp116PostPResidualBound_of_sourceBound
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (postPSourceWeight : σ → ℝ)
    (postPAmplitude : ℝ)
    (pWeight : σ → ιD → ιP → ℝ)
    (hsource :
      CMP116PostPResidualSourceBound
        R postPSourceWeight postPAmplitude pWeight)
    (hmajorant :
      ∀ Z,
        postPAmplitude * postPSourceWeight Z ≤
          (hp.C3 * hp.epsilon1) *
            balabanCMP116Lemma3Weight
              hp.blockScale hp.delta hp.kappa sourceMetric Z)
    (hpWeight_nonneg :
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D → 0 ≤ pWeight Z D P) :
    CMP116PostPResidualBound hp R sourceMetric pWeight := by
  intro Z D hD P hP
  exact
    (hsource Z D hD P hP).trans
      (mul_le_mul_of_nonneg_right
        (hmajorant Z)
        (hpWeight_nonneg Z D hD P hP))

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

/-- The split normalized `Z0/Z0'` residual-stage route packages into the direct
combined post-`P` residual predicate.

This is an interface bridge only: it proves that the older split route is a
special case of `CMP116PostPResidualBound`.  It does not source-identify either
residual estimate. -/
theorem cmp116PostPResidualBound_of_residualStages
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (z0Weight : σ → ιD → ιP → ιZ0 → ℝ)
    (z0PrimeWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ)
    (hZ0sum :
      CMP116Z0ResidualSummability
        R.DIndex R.PIndex R.Z0Index z0Weight)
    (hZ0PrimeSum :
      CMP116Z0PrimeResidualSummability
        R.DIndex R.PIndex R.Z0Index R.Z0PrimeIndex z0PrimeWeight)
    (hC3epsilon1_nonneg : 0 ≤ hp.C3 * hp.epsilon1)
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
                    pWeight Z D P) *
                  z0Weight Z D P Z0) *
                  z0PrimeWeight Z D P Z0 Z0') ) :
    CMP116PostPResidualBound hp R sourceMetric pWeight := by
  intro Z D hD P hP
  exact
    cmp116H_postP_sum_le_of_residualStages
      R
      (fun Z D P =>
        ((hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z) *
          pWeight Z D P)
      z0Weight z0PrimeWeight
      hZ0sum hZ0PrimeSum
      (fun Z D hD P hP =>
        mul_nonneg
          (mul_nonneg hC3epsilon1_nonneg
            (balabanCMP116Lemma3Weight_nonneg
              hp.blockScale hp.delta hp.kappa sourceMetric Z))
          (hpWeight_nonneg Z D hD P hP))
      hz0Weight_nonneg
      hfactor
      Z D hD P hP

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

/-- A P-stage budget plus a direct combined post-`P` residual budget implies
the post-`D` residual budget required by the equation-(2.29) consumer.

Unlike `cmp116H_postD_sum_le_of_pStageResidualStages`, this route does not
split the last two residual estimates into normalized `Z0` and `Z0'` stages.
It is intended for source statements, such as CMP116 pages 19--20, where the
last residual resummations are controlled as a combined finite estimate or in a
different summation order. -/
theorem cmp116H_postD_sum_le_of_pStagePostPResidualBound
    {σ ιD ιP ιZ0 ιZ0' ιY Ψ Φ : Type*}
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (pWeight : σ → ιD → ιP → ℝ)
    (hPStage :
      CMP116PStageSummability
        R.DIndex R.PIndex pWeight
        (fun Z D =>
          Finset.prod (DParts Z D)
            (cmp116Eq229Weight
              alpha6 hp.delta hp.kappa (eq229Metric Z))))
    (hpostP :
      CMP116PostPResidualBound hp R sourceMetric pWeight) :
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
  exact
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

/-- Equation (2.29), a P-stage budget, and a direct combined post-`P`
residual budget give the finite CMP116 `H` term-weight budget.

This route deliberately avoids naming separate source equations for the `Z0`
and `Z0'` normalized residual predicates. -/
theorem cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound
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
    (hpostP :
      CMP116PostPResidualBound hp R sourceMetric pWeight) :
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
      (cmp116H_postD_sum_le_of_pStagePostPResidualBound
        hp R sourceMetric DParts alpha6 eq229Metric
        pWeight hPStage hpostP)

/-- Eq. (2.29), an explicit P-stage budget, and a direct combined post-`P`
residual budget feed the theorem-backed CMP116 Lemma 3 activity estimate.

The theorem keeps the activity identification, complex termwise estimate,
P-stage budget, and combined post-`P` residual estimate as explicit
hypotheses. -/
theorem cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound
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
    (hpostP :
      CMP116PostPResidualBound hp R sourceMetric pWeight)
    (hglobal :
      ∀ Z ψ φ,
        (physicalActivity Z).globalEval ψ φ =
          balabanCMP116H R Z ψ φ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) :
    CMP116Lemma3ActivityEstimate
      physicalActivity sourceMetric hp.blockScale
      hp.C3 hp.epsilon1 hp.delta hp.kappa :=
  cmp116Lemma3ActivityEstimate_of_resummation
    hp R sourceMetric physicalActivity
    hglobal hterm
    (cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound
      hp R sourceMetric DParts alpha6 eq229Metric
      pWeight hEq229 hPStage hpostP)

end YangMills.RG
