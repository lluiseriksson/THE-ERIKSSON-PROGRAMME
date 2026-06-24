/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourceTheorem

/-!
# CMP116 Lemma 3 resummed-activity interface

This module starts the theorem-fed route from Balaban CMP116 pre-Lemma-3
summands to the already exposed Lemma 3 activity estimate interface.

Honest scope: this file does not prove the analytic CMP116 resummation from
the paper's constants.  It proves the final norm step from explicitly supplied
termwise summand bounds and an explicitly supplied summed-weight budget.  The
source extraction still has to derive those inputs from CMP116 equations
(2.27), (2.29)--(2.32), (2.34), (2.36), and (2.37).
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Primitive CMP116 Lemma 3 parameters before the exact source hierarchy is
formalized.

The fields are intentionally primitive.  There is no `H_decay`,
`raw_pointwise_decay`, or equivalent conclusion field here. -/
structure CMP116Lemma3Parameters where
  blockScale : ℕ
  delta : ℝ
  epsilon1 : ℝ
  epsilon2 : ℝ
  C3 : ℝ
  kappa : ℝ
  kappa1 : ℝ
  amplitude_nonneg : 0 ≤ C3 * epsilon1
  epsilon2_nonneg : 0 ≤ epsilon2
  scale_margin :
    2 * (blockScale : ℝ) * kappa ≤ (kappa1 - 1) / 2

/-- Finite pre-Lemma resummation data for a fixed source polymer/activity
label.

The four finite index families model the successive source sums over the
objects denoted around CMP116 Lemma 3 by `D`, `P`, `Z0`, and `Z0'`.  The
summands and weights are not assumed to satisfy a final decay estimate in the
record; that estimate is supplied to the theorem below as a separate
pre-Lemma summed-weight budget. -/
structure CMP116HResummation
    (σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*) where
  DIndex : σ → Finset ιD
  PIndex : σ → Finset ιP
  Z0Index : σ → Finset ιZ0
  Z0PrimeIndex : σ → Finset ιZ0'
  summand : σ → ιD → ιP → ιZ0 → ιZ0' → Ψ → Φ → ℂ
  termWeight : σ → ιD → ιP → ιZ0 → ιZ0' → ℝ

/-- The flattened finite index set for the four source summations entering the
resummed activity `H(Z)`. -/
def cmp116HIndexFinset
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) :
    Finset ((ιD × ιP) × (ιZ0 × ιZ0')) :=
  ((R.DIndex Z).product (R.PIndex Z)).product
    ((R.Z0Index Z).product (R.Z0PrimeIndex Z))

/-- The resummed CMP116 activity `H(Z)` represented by the finite pre-Lemma
summation data. -/
noncomputable def balabanCMP116H
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (Z : σ) (ψ : Ψ) (φ : Φ) : ℂ :=
  Finset.sum (cmp116HIndexFinset R Z)
    (fun x => R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ)

/-- Final norm step for CMP116 Lemma 3.

This is the theorem-fed bridge from termwise source bounds plus a pre-Lemma
summed-weight budget to the displayed Lemma 3 estimate.  The hypotheses are
not a bound on `balabanCMP116H` itself. -/
theorem norm_balabanCMP116H_le_lemma3
    {σ ιD ιP ιZ0 ιZ0' Ψ Φ : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    (hp : CMP116Lemma3Parameters)
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0' Ψ Φ)
    (sourceMetric : σ → ℕ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hbudget :
      ∀ Z,
        Finset.sum (cmp116HIndexFinset R Z)
          (fun x => R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) ≤
          (hp.C3 * hp.epsilon1) *
            balabanCMP116Lemma3Weight
              hp.blockScale hp.delta hp.kappa sourceMetric Z) :
    ∀ Z ψ φ,
      ‖balabanCMP116H R Z ψ φ‖ ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z := by
  intro Z ψ φ
  unfold balabanCMP116H
  calc
    ‖Finset.sum (cmp116HIndexFinset R Z)
        (fun x => R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ)‖
        ≤ Finset.sum (cmp116HIndexFinset R Z)
            (fun x => ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖) :=
      norm_sum_le (cmp116HIndexFinset R Z)
        (fun x => R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ)
    _ ≤ Finset.sum (cmp116HIndexFinset R Z)
          (fun x => R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) :=
      Finset.sum_le_sum (fun x hx => hterm Z x hx ψ φ)
    _ ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight
            hp.blockScale hp.delta hp.kappa sourceMetric Z :=
      hbudget Z

/-- A source identification of the resummed `H(Z)` with a physical local
activity turns the theorem-fed Lemma 3 bound into the existing
`CMP116Lemma3ActivityEstimate` object. -/
theorem cmp116Lemma3ActivityEstimate_of_resummation
    {σ ιD ιP ιZ0 ιZ0' : Type*}
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
    (hglobal :
      ∀ Z ψ φ,
        (physicalActivity Z).globalEval ψ φ =
          balabanCMP116H R Z ψ φ)
    (hterm :
      ∀ Z x, x ∈ cmp116HIndexFinset R Z →
        ∀ ψ φ,
          ‖R.summand Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
            R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hbudget :
      ∀ Z,
        Finset.sum (cmp116HIndexFinset R Z)
          (fun x => R.termWeight Z x.1.1 x.1.2 x.2.1 x.2.2) ≤
          (hp.C3 * hp.epsilon1) *
            balabanCMP116Lemma3Weight
              hp.blockScale hp.delta hp.kappa sourceMetric Z) :
    CMP116Lemma3ActivityEstimate
      physicalActivity sourceMetric hp.blockScale
      hp.C3 hp.epsilon1 hp.delta hp.kappa where
  amplitude_nonneg := hp.amplitude_nonneg
  pointwise_decay := by
    intro Z ψ φ
    calc
      ‖(physicalActivity Z).globalEval ψ φ‖ =
          ‖balabanCMP116H R Z ψ φ‖ := by
        rw [hglobal Z ψ φ]
      _ ≤
          (hp.C3 * hp.epsilon1) *
            balabanCMP116Lemma3Weight
              hp.blockScale hp.delta hp.kappa sourceMetric Z :=
        norm_balabanCMP116H_le_lemma3 hp R sourceMetric
          hterm hbudget Z ψ φ

end YangMills.RG
