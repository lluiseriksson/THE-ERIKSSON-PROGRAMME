/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries

/-!
# CMP116 Lemma 1 equation (1.11): weakened-propagator bound

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and the result has not yet been verified by the Lean compiler.

CMP116 expands each of the propagators `H(s)`, `G(s)`, and `H₀(s)` as a
generalized random-walk series.  A walk is weakened once for every parameter
connected with the union of its localization domains.  Equation (1.11) then
uses the literal dichotomy

* at most `2^4 = 16` connected parameters, costing `exp (16 * kappa1)`;
* more than `16`, where the tree-length estimate absorbs the full weakening
  factor when `kappa1 ≤ delta1 * M`.

This module formalizes that deduction for one propagator.  The propagator is
defined internally as the complex weakened `tsum`; no preselected family
`sigma ↦ P sigma` is accepted.  Its unweakened value and coordinatewise
analyticity are inherited from the exact random-walk series.

Honest scope: `source_walk_bound`, `long_walk_geometry`, and the summable
base-weight budget are the CMP99 `(3.108)`-shaped source input quoted in
CMP116 `(1.7)`--`(1.11)`.  The concrete identifications with the three
physical propagators are separate specializations.  In particular this file
does not identify the source's `H₀(s)` with either the rectangular minimizer
`H(s)` or the square covariance `G(s)`.

Primary source: T. Balaban, *Renormalization Group Approach to Lattice Gauge
Field Theory II*, CMP116, equations (1.6)--(1.11), especially the printed
threshold `m > 2^4` on page 5.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w

variable {Delta : Type u} {Walk : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The literal radius-`exp kappa1` polydisc of CMP116 equation (1.11). -/
def cmp116Lemma1WeakeningPolydisc
    (kappa1 : ℝ) : Set (Delta → ℂ) :=
  {sigma | ∀ d, ‖sigma d‖ ≤ Real.exp kappa1}

/-- Source data for one weakened propagator.  The term and active carrier are
parameters of the type, so the certificate cannot hide a different operator
family in a field.  The remaining fields are precisely the per-walk source
estimate and the summable walk-count budget. -/
structure CMP116Lemma1WeakenedPropagatorCertificate
    (active : Walk → Finset Delta)
    (term : Walk → E)
    (treeLength : Walk → ℕ)
    (baseWeight : Walk → ℝ)
    (B0 delta0 delta1 M kappa1 : ℝ) : Prop where
  baseWeight_nonneg : ∀ walk, 0 ≤ baseWeight walk
  baseWeight_summable : Summable baseWeight
  baseWeight_tsum_le : (∑' walk, baseWeight walk) ≤ B0
  B0_nonneg : 0 ≤ B0
  delta0_nonneg : 0 ≤ delta0
  kappa1_nonneg : 0 ≤ kappa1
  scale_budget : kappa1 ≤ delta1 * M
  source_walk_bound : ∀ walk,
    ‖term walk‖ ≤
      baseWeight walk *
        Real.exp (-(delta0 * (treeLength walk : ℝ)))
  long_walk_geometry : ∀ walk,
    16 < (active walk).card →
      delta1 * ((active walk).card : ℝ) * M ≤
        delta0 * (treeLength walk : ℝ)

namespace CMP116Lemma1WeakenedPropagatorCertificate

variable
    {active : Walk → Finset Delta}
    {term : Walk → E}
    {treeLength : Walk → ℕ}
    {baseWeight : Walk → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1WeakenedPropagatorCertificate
      active term treeLength baseWeight B0 delta0 delta1 M kappa1)

include C

/-- The source split at `m = 2^4` bounds the weakening exponent uniformly by
`16 * kappa1`.  The number `16` and the tree-length absorption are kept
separate; no repository `/24` animal normalization enters this lemma. -/
theorem walkExponent_le_sixteen
    (walk : Walk) :
    kappa1 * ((active walk).card : ℝ) -
        delta0 * (treeLength walk : ℝ) ≤
      16 * kappa1 := by
  by_cases hshort : (active walk).card ≤ 16
  · have hm : ((active walk).card : ℝ) ≤ 16 := by
      exact_mod_cast hshort
    have hd : 0 ≤ delta0 * (treeLength walk : ℝ) :=
      mul_nonneg C.delta0_nonneg (Nat.cast_nonneg _)
    nlinarith [C.kappa1_nonneg]
  · have hlong : 16 < (active walk).card := by omega
    have hm0 : 0 ≤ ((active walk).card : ℝ) := Nat.cast_nonneg _
    have hscale :=
      mul_le_mul_of_nonneg_right C.scale_budget hm0
    have hgeom := C.long_walk_geometry walk hlong
    have habsorb :
        kappa1 * ((active walk).card : ℝ) ≤
          delta0 * (treeLength walk : ℝ) := by
      calc
        kappa1 * ((active walk).card : ℝ) ≤
            (delta1 * M) * ((active walk).card : ℝ) := hscale
        _ = delta1 * ((active walk).card : ℝ) * M := by ring
        _ ≤ delta0 * (treeLength walk : ℝ) := hgeom
    nlinarith [C.kappa1_nonneg]

/-- Exponential form of the printed short/long-walk dichotomy. -/
theorem exp_walkExponent_le
    (walk : Walk) :
    Real.exp
        (kappa1 * ((active walk).card : ℝ) -
          delta0 * (treeLength walk : ℝ)) ≤
      Real.exp (16 * kappa1) :=
  Real.exp_le_exp.mpr (C.walkExponent_le_sixteen walk)

/-- The source `(3.108)` term bound and the printed dichotomy control one
radial-majorant summand. -/
theorem radialMajorant_le
    (walk : Walk) :
    (Real.exp kappa1) ^ (active walk).card * ‖term walk‖ ≤
      Real.exp (16 * kappa1) * baseWeight walk := by
  calc
    (Real.exp kappa1) ^ (active walk).card * ‖term walk‖ ≤
        (Real.exp kappa1) ^ (active walk).card *
          (baseWeight walk *
            Real.exp (-(delta0 * (treeLength walk : ℝ)))) :=
      mul_le_mul_of_nonneg_left (C.source_walk_bound walk)
        (pow_nonneg (Real.exp_nonneg _) _)
    _ = baseWeight walk *
        Real.exp
          (kappa1 * ((active walk).card : ℝ) -
            delta0 * (treeLength walk : ℝ)) := by
      rw [← Real.exp_nat_mul]
      calc
        Real.exp (((active walk).card : ℝ) * kappa1) *
              (baseWeight walk *
                Real.exp (-(delta0 * (treeLength walk : ℝ)))) =
            baseWeight walk *
              (Real.exp (((active walk).card : ℝ) * kappa1) *
                Real.exp (-(delta0 * (treeLength walk : ℝ)))) := by ring
        _ = baseWeight walk *
              Real.exp
                ((((active walk).card : ℝ) * kappa1) +
                  (-(delta0 * (treeLength walk : ℝ)))) := by
            rw [Real.exp_add]
        _ = baseWeight walk *
              Real.exp
                (kappa1 * ((active walk).card : ℝ) -
                  delta0 * (treeLength walk : ℝ)) := by
            congr 2
            ring
    _ ≤ baseWeight walk * Real.exp (16 * kappa1) :=
      mul_le_mul_of_nonneg_left
        (C.exp_walkExponent_le walk) (C.baseWeight_nonneg walk)
    _ = Real.exp (16 * kappa1) * baseWeight walk := by ring

/-- The radial majorant required by the generic complex weakened series is
summable. -/
theorem summable_radialMajorant :
    Summable fun walk =>
      (Real.exp kappa1) ^ (active walk).card * ‖term walk‖ := by
  exact Summable.of_nonneg_of_le
    (fun walk => mul_nonneg (pow_nonneg (Real.exp_nonneg _) _)
      (norm_nonneg _))
    (fun walk => C.radialMajorant_le walk)
    (C.baseWeight_summable.mul_left (Real.exp (16 * kappa1)))

/-- The weakened propagator is the literal complex random-walk `tsum`. -/
noncomputable def propagator
    (_C : CMP116Lemma1WeakenedPropagatorCertificate
      active term treeLength baseWeight B0 delta0 delta1 M kappa1)
    (sigma : Delta → ℂ) : E :=
  cmp116ComplexWeakenedRandomWalkSeries active term sigma

/-- At full coupling the weakened propagator is exactly the original walk
series, not an independently supplied operator. -/
theorem propagator_one :
    C.propagator (fun _ => 1) = ∑' walk, term walk := by
  simpa [propagator] using
    (cmp116ComplexWeakenedRandomWalkSeries_one active term)

/-- Equation (1.11): uniform norm bound on the whole source polydisc. -/
theorem norm_propagator_le
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    ‖C.propagator sigma‖ ≤ B0 * Real.exp (16 * kappa1) := by
  let radius : Delta → ℝ := fun _ => Real.exp kappa1 - 1
  have hR : 1 ≤ Real.exp kappa1 := Real.one_le_exp C.kappa1_nonneg
  have hradius : ∀ d, 0 ≤ radius d := by
    intro d
    exact sub_nonneg.mpr hR
  have hsigma' :
      sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius := by
    intro d
    simpa [radius] using hsigma d
  have hcap : ∀ walk d, d ∈ active walk →
      1 + radius d ≤ Real.exp kappa1 := by
    intro walk d hd
    simp [radius]
  have hseries :=
    norm_cmp116ComplexWeakenedRandomWalkSeries_le_tsum_majorant
      active term sigma radius (Real.exp kappa1)
      (Real.exp_nonneg _) hsigma' hcap C.summable_radialMajorant
  have htsum :
      (∑' walk,
          (Real.exp kappa1) ^ (active walk).card * ‖term walk‖) ≤
        ∑' walk, Real.exp (16 * kappa1) * baseWeight walk :=
    Summable.tsum_le_tsum
      (fun walk => C.radialMajorant_le walk)
      C.summable_radialMajorant
      (C.baseWeight_summable.mul_left (Real.exp (16 * kappa1)))
  calc
    ‖C.propagator sigma‖ ≤
        ∑' walk,
          (Real.exp kappa1) ^ (active walk).card * ‖term walk‖ := by
      simpa [propagator] using hseries
    _ ≤ ∑' walk, Real.exp (16 * kappa1) * baseWeight walk := htsum
    _ = Real.exp (16 * kappa1) * ∑' walk, baseWeight walk :=
      tsum_mul_left
    _ ≤ Real.exp (16 * kappa1) * B0 :=
      mul_le_mul_of_nonneg_left C.baseWeight_tsum_le (Real.exp_nonneg _)
    _ = B0 * Real.exp (16 * kappa1) := by ring

/-- Coordinatewise analyticity of the same internally constructed family.
This is the exact affine-coordinate conclusion needed by the later Cauchy
extraction; no differentiation of a freely supplied propagator is assumed. -/
theorem hasDerivAt_propagator_update
    [DecidableEq Delta]
    (sigma : Delta → ℂ) (d : Delta)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1)
    (z : ℂ) :
    HasDerivAt
      (fun t => C.propagator (Function.update sigma d t))
      (cmp116ComplexWeakenedRandomWalkSeriesDerivative
        active term sigma d)
      z := by
  let radius : Delta → ℝ := fun _ => Real.exp kappa1 - 1
  have hR : 1 ≤ Real.exp kappa1 := Real.one_le_exp C.kappa1_nonneg
  have hradius : ∀ x, 0 ≤ radius x := by
    intro x
    exact sub_nonneg.mpr hR
  have hsigma' :
      sigma ∈ cmp116ComplexShiftedWeakeningPolydisc radius := by
    intro x
    simpa [radius] using hsigma x
  have hcap : ∀ walk x, x ∈ active walk →
      1 + radius x ≤ Real.exp kappa1 := by
    intro walk x hx
    simp [radius]
  simpa [propagator] using
    (hasDerivAt_cmp116ComplexWeakenedRandomWalkSeries_update
      active term sigma d radius (Real.exp kappa1)
      hradius hR hsigma' hcap C.summable_radialMajorant z)

end CMP116Lemma1WeakenedPropagatorCertificate

section OperatorApplication

universe x y

variable {X : Type x} {Y : Type y}
variable [NormedAddCommGroup X] [NormedSpace ℂ X]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Operator-action form of (1.11), matching the printed
`B0 * exp(16*kappa1) * |X|` conclusion. -/
theorem CMP116Lemma1WeakenedPropagatorCertificate.norm_propagator_apply_le
    {active : Walk → Finset Delta}
    {term : Walk → (X →L[ℂ] Y)}
    {treeLength : Walk → ℕ}
    {baseWeight : Walk → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1WeakenedPropagatorCertificate
      active term treeLength baseWeight B0 delta0 delta1 M kappa1)
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1)
    (x : X) :
    ‖C.propagator sigma x‖ ≤
      (B0 * Real.exp (16 * kappa1)) * ‖x‖ := by
  calc
    ‖C.propagator sigma x‖ ≤ ‖C.propagator sigma‖ * ‖x‖ :=
      (C.propagator sigma).le_opNorm x
    _ ≤ (B0 * Real.exp (16 * kappa1)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (C.norm_propagator_le sigma hsigma) (norm_nonneg x)

end OperatorApplication

end

end YangMills.RG
