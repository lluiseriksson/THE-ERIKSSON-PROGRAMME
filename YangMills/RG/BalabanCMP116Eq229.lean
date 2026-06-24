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
residual post-D budget or the analytic Lemma 3 constants.
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

/-- The fixed-`D` product appearing in CMP116 equation (2.29). -/
noncomputable def cmp116Eq229Product
    {σ ιD ιY : Type*}
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (Z : σ) (D : ιD) : ℝ :=
  Finset.prod (DParts Z D)
    (cmp116Eq229Weight alpha6 delta kappa (metric Z))

/-- The CMP116 (2.29) weight is nonnegative when `alpha_6` is nonnegative. -/
theorem cmp116Eq229Weight_nonneg
    {ιY : Type*}
    {alpha6 delta kappa : ℝ}
    {metric : ιY → ℕ}
    (halpha6 : 0 ≤ alpha6)
    (Y : ιY) :
    0 ≤ cmp116Eq229Weight alpha6 delta kappa metric Y := by
  exact mul_nonneg halpha6 (Real.exp_nonneg _)

/-- The CMP116 (2.29) fixed-`D` product is nonnegative when `alpha_6` is
nonnegative. -/
theorem cmp116Eq229Product_nonneg
    {σ ιD ιY : Type*}
    {DParts : σ → ιD → Finset ιY}
    {alpha6 delta kappa : ℝ}
    {metric : σ → ιY → ℕ}
    (halpha6 : 0 ≤ alpha6)
    (Z : σ) (D : ιD) :
    0 ≤ cmp116Eq229Product DParts alpha6 delta kappa metric Z D := by
  exact
    Finset.prod_nonneg
      (fun Y _ =>
        cmp116Eq229Weight_nonneg
          (metric := metric Z) halpha6 Y)

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

/-- A finite post-D `P`-stage summability predicate.

The budget is explicit.  In the CMP116 Lemma-3 route it will be instantiated
with the fixed-D product appearing in equation (2.29).

This declaration does not assert that a particular CMP116 equation proves the
predicate. -/
def CMP116PStageSummability
    {σ ιD ιP : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (pWeight : σ → ιD → ιP → ℝ)
    (budget : σ → ιD → ℝ) : Prop :=
  ∀ Z D, D ∈ DIndex Z →
    Finset.sum (PIndex Z D) (fun P => pWeight Z D P) ≤
      budget Z D

/-- The `P`-stage summability budget converts fixed-P residual
`Z0 -> Z0'` estimates into the complete post-D bound.

This is finite summation bookkeeping only.  It does not prove the P-stage
summability predicate or either residual localization estimate. -/
theorem cmp116H_postDSum_le_of_pStage
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
      ∀ Z D, D ∈ R.DIndex Z →
        ∀ P, P ∈ R.PIndex Z D →
          Finset.sum (R.Z0Index Z D P) (fun Z0 =>
            Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
              R.termWeight Z D P Z0 Z0')) ≤
            ((hp.C3 * hp.epsilon1) *
              balabanCMP116Lemma3Weight
                hp.blockScale hp.delta hp.kappa sourceMetric Z) *
              pWeight Z D P) :
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
  intro Z D hD
  let A : ℝ :=
    (hp.C3 * hp.epsilon1) *
      balabanCMP116Lemma3Weight
        hp.blockScale hp.delta hp.kappa sourceMetric Z
  have hA_nonneg : 0 ≤ A := by
    exact
      mul_nonneg hp.amplitude_nonneg
        (balabanCMP116Lemma3Weight_nonneg
          hp.blockScale hp.delta hp.kappa sourceMetric Z)
  calc
    Finset.sum (R.PIndex Z D) (fun P =>
        Finset.sum (R.Z0Index Z D P) (fun Z0 =>
          Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
            R.termWeight Z D P Z0 Z0')))
        ≤
      Finset.sum (R.PIndex Z D)
        (fun P => A * pWeight Z D P) := by
          exact Finset.sum_le_sum (fun P hP => by
            simpa [A] using hpostP Z D hD P hP)
    _ =
      A * Finset.sum (R.PIndex Z D)
        (fun P => pWeight Z D P) := by
          simp [Finset.mul_sum]
    _ ≤
      A * Finset.prod (DParts Z D)
        (cmp116Eq229Weight
          alpha6 hp.delta hp.kappa (eq229Metric Z)) := by
          exact
            mul_le_mul_of_nonneg_left
              (hPStage Z D hD) hA_nonneg
    _ =
      ((hp.C3 * hp.epsilon1) *
        balabanCMP116Lemma3Weight
          hp.blockScale hp.delta hp.kappa sourceMetric Z) *
        Finset.prod (DParts Z D)
          (cmp116Eq229Weight
            alpha6 hp.delta hp.kappa (eq229Metric Z)) := by
          rfl

/-- The flattened CMP116 Lemma-3 index set has the same term-weight sum as the
source-shaped nested `D -> P -> Z0 -> Z0'` sum. -/
theorem cmp116H_termWeightSum_eq_nested
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ) :
    ∀ Z,
      Finset.sum (cmp116HIndexFinset R Z)
        (fun x =>
          R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) =
        Finset.sum (R.DIndex Z) (fun D =>
          Finset.sum (R.PIndex Z D) (fun P =>
            Finset.sum (R.Z0Index Z D P) (fun Z0 =>
              Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
                R.termWeight Z D P Z0 Z0')))) := by
  intro Z
  classical
  have hDdisjoint :
      Set.PairwiseDisjoint (R.DIndex Z : Set ιD) (fun D =>
        (R.PIndex Z D).biUnion fun P =>
          (R.Z0Index Z D P).biUnion fun Z0 =>
            (R.Z0PrimeIndex Z D P Z0).map
              ⟨fun Z0' => ((D, P), (Z0, Z0')),
                by
                  intro a b h
                  simpa using congrArg (fun y => y.2.2) h⟩) := by
    intro D _ E _ hDE
    refine Finset.disjoint_left.2 ?_
    intro x hxD hxE
    simp at hxD hxE
    rcases hxD with ⟨P, _, Z0, _, Z0', _, hxD⟩
    rcases hxE with ⟨P', _, Z1, _, Z1', _, hxE⟩
    apply hDE
    have hx : ((D, P), (Z0, Z0')) = ((E, P'), (Z1, Z1')) := by
      exact hxD.trans hxE.symm
    exact congrArg (fun y => y.1.1) hx
  unfold cmp116HIndexFinset
  rw [Finset.sum_biUnion hDdisjoint]
  apply Finset.sum_congr rfl
  intro D _
  have hPdisjoint :
      Set.PairwiseDisjoint (R.PIndex Z D : Set ιP) (fun P =>
        (R.Z0Index Z D P).biUnion fun Z0 =>
          (R.Z0PrimeIndex Z D P Z0).map
            ⟨fun Z0' => ((D, P), (Z0, Z0')),
              by
                intro a b h
                simpa using congrArg (fun y => y.2.2) h⟩) := by
    intro P _ Q _ hPQ
    refine Finset.disjoint_left.2 ?_
    intro x hxP hxQ
    simp at hxP hxQ
    rcases hxP with ⟨Z0, _, Z0', _, hxP⟩
    rcases hxQ with ⟨Z1, _, Z1', _, hxQ⟩
    apply hPQ
    have hx : ((D, P), (Z0, Z0')) = ((D, Q), (Z1, Z1')) := by
      exact hxP.trans hxQ.symm
    exact congrArg (fun y => y.1.2) hx
  rw [Finset.sum_biUnion hPdisjoint]
  apply Finset.sum_congr rfl
  intro P _
  have hZ0disjoint :
      Set.PairwiseDisjoint (R.Z0Index Z D P : Set ιZ0) (fun Z0 =>
        (R.Z0PrimeIndex Z D P Z0).map
          ⟨fun Z0' => ((D, P), (Z0, Z0')),
            by
              intro a b h
              simpa using congrArg (fun y => y.2.2) h⟩) := by
    intro Z0 _ Z1 _ hZ01
    refine Finset.disjoint_left.2 ?_
    intro x hxZ0 hxZ1
    simp at hxZ0 hxZ1
    rcases hxZ0 with ⟨Z0', _, hxZ0⟩
    rcases hxZ1 with ⟨Z1', _, hxZ1⟩
    apply hZ01
    have hx : ((D, P), (Z0, Z0')) = ((D, P), (Z1, Z1')) := by
      exact hxZ0.trans hxZ1.symm
    exact congrArg (fun y => y.2.1) hx
  rw [Finset.sum_biUnion hZ0disjoint]
  apply Finset.sum_congr rfl
  intro Z0 _
  rw [Finset.sum_map]
  simp

/-- CMP116 equation (2.29) discharges the outer `D`-sum in the finite
Lemma-3 term-weight budget.

The hypothesis `hpostD` retains the complete residual resummation over `P`,
`Z0`, and `Z0'`.  This theorem proves only the finite budget assembly; it does
not prove those residual estimates or the analytic CMP116 constants. -/
theorem cmp116H_termWeightSum_le_of_eq229
    {σ ιD ιP ιZ0 ιZ0' ιY Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : σ → ιY → ℕ)
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hpostD :
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
                alpha6 hp.delta hp.kappa (eq229Metric Z))) :
    ∀ Z,
      Finset.sum (cmp116HIndexFinset R Z)
        (fun x =>
          R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z := by
  intro Z
  let B : σ → Unit → ℝ := fun Z _ =>
    (hp.C3 * hp.epsilon1) *
      balabanCMP116Lemma3Weight
        hp.blockScale hp.delta hp.kappa sourceMetric Z
  let T : σ → ιD → Unit → ℝ := fun Z D _ =>
    Finset.sum (R.PIndex Z D) (fun P =>
      Finset.sum (R.Z0Index Z D P) (fun Z0 =>
        Finset.sum (R.Z0PrimeIndex Z D P Z0) (fun Z0' =>
          R.termWeight Z D P Z0 Z0')))
  have hDstage :
      Finset.sum (R.DIndex Z) (fun D => T Z D ()) ≤ B Z () := by
    exact
      cmp116_DStage_sum_le_of_eq229
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric
        B T hEq229
        (fun Z _ =>
          mul_nonneg hp.amplitude_nonneg
            (balabanCMP116Lemma3Weight_nonneg
              hp.blockScale hp.delta hp.kappa sourceMetric Z))
        (fun Z D hD _ => hpostD Z D hD)
        Z ()
  calc
    Finset.sum (cmp116HIndexFinset R Z)
        (fun x =>
          R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
        =
      Finset.sum (R.DIndex Z) (fun D => T Z D ()) := by
        simpa [T] using cmp116H_termWeightSum_eq_nested R Z
    _ ≤ B Z () := hDstage
    _ =
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z := rfl

/-- Eq. (2.29), plus an explicit post-D residual bound, feeds the theorem-fed
CMP116 Lemma 3 activity estimate without a separate monolithic `hbudget`
premise.

This theorem still keeps the complex-valued termwise estimate and all residual
`P/Z0/Z0'` resummation estimates as explicit hypotheses. -/
theorem cmp116Lemma3ActivityEstimate_of_eq229_postD
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
    (hEq229 :
      CMP116Eq229Summability
        R.DIndex DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hglobal :
      ∀ Z ψ φ,
        (physicalActivity Z).globalEval ψ φ =
          balabanCMP116H R Z ψ φ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hpostD :
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
                alpha6 hp.delta hp.kappa (eq229Metric Z))) :
    CMP116Lemma3ActivityEstimate
      physicalActivity sourceMetric hp.blockScale
      hp.C3 hp.epsilon1 hp.delta hp.kappa :=
  cmp116Lemma3ActivityEstimate_of_resummation
    hp R sourceMetric physicalActivity
    hglobal hterm
    (cmp116H_termWeightSum_le_of_eq229
      hp R sourceMetric DParts alpha6 eq229Metric hEq229 hpostD)

end YangMills.RG
