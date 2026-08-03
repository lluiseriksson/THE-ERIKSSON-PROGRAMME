/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WeakeningMultiplicityPowersetMajorant
import YangMills.RG.BalabanCMP116Lemma1WeakenedPropagatorBound

/-!
# Auxiliary multiplicity-aware weakened-series bound

The repository's algebraically weakened minimizer contains products of
independently weakened factors.  Overlapping carriers give repeated powers
of one weakening coordinate, so the square-free L1 propagator certificate is
not applicable to that auxiliary object.  This module proves a corresponding
norm-only deduction for finitely supported natural multiplicities.

The propagator is constructed internally as the multiplicity-weighted `tsum`.
The source input is one summable base-weight budget over the already expanded
walk index, together with a long-walk inequality for the **total multiplicity
degree**.  Thus a physical instantiation must account for its finite powerset
cost in `baseWeight` and must prove the source-to-series degree geometry.  No
identification with the printed CMP116 integer `m` is made here.

SOURCE-DICTIONARY WARNING: CMP116 defines the printed `H(s)` directly from
generalized random walks, with one factor per distinct cube in the union of
the walk's localization domains.  Its monomials are squarefree.  This module
therefore proves an equation-(1.11)-shaped auxiliary estimate, not the
physical specialization of printed equation (1.11).  It must not be used to
replace the distinct-cube dictionary by total multiplicity degree.

Unlike a square-free monomial, a multiplicity monomial is generally not
affine in one coordinate.  This brick proves the uniform equation-(1.11) norm
bound needed before L2; coordinatewise holomorphy and the later Cauchy step
remain separate.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v w

variable {Delta : Type u} {Walk : Type v} {E : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The countable complex series with every weakening occurrence retained. -/
noncomputable def cmp116ComplexWeakeningMultiplicitySeries
    (multiplicity : Walk → Delta →₀ ℕ) (term : Walk → E)
    (sigma : Delta → ℂ) : E :=
  ∑' walk,
    cmp116ComplexWeakeningMultiplicityMonomial (multiplicity walk) sigma •
      term walk

/-- The total-degree radial majorant makes the multiplicity series summable. -/
theorem summable_cmp116ComplexWeakeningMultiplicitySeries
    (multiplicity : Walk → Delta →₀ ℕ) (term : Walk → E)
    (sigma : Delta → ℂ) (R : ℝ)
    (hsigma : ∀ walk d, d ∈ (multiplicity walk).support → ‖sigma d‖ ≤ R)
    (hmajor : Summable fun walk =>
      R ^ cmp116WeakeningMultiplicityDegree (multiplicity walk) *
        ‖term walk‖) :
    Summable fun walk =>
      cmp116ComplexWeakeningMultiplicityMonomial
          (multiplicity walk) sigma • term walk :=
  Summable.of_norm_bounded hmajor fun walk =>
    norm_cmp116ComplexWeakeningMultiplicityTerm_le_radialMajorant
      (multiplicity walk) (term walk) sigma R (hsigma walk)

/-- Uniform norm bound by the `tsum` of total-degree radial majorants. -/
theorem norm_cmp116ComplexWeakeningMultiplicitySeries_le_tsum_majorant
    (multiplicity : Walk → Delta →₀ ℕ) (term : Walk → E)
    (sigma : Delta → ℂ) (R : ℝ)
    (hsigma : ∀ walk d, d ∈ (multiplicity walk).support → ‖sigma d‖ ≤ R)
    (hmajor : Summable fun walk =>
      R ^ cmp116WeakeningMultiplicityDegree (multiplicity walk) *
        ‖term walk‖) :
    ‖cmp116ComplexWeakeningMultiplicitySeries multiplicity term sigma‖ ≤
      ∑' walk,
        R ^ cmp116WeakeningMultiplicityDegree (multiplicity walk) *
          ‖term walk‖ := by
  have hnorm : Summable fun walk =>
      ‖cmp116ComplexWeakeningMultiplicityMonomial
          (multiplicity walk) sigma • term walk‖ :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun walk =>
        norm_cmp116ComplexWeakeningMultiplicityTerm_le_radialMajorant
          (multiplicity walk) (term walk) sigma R (hsigma walk))
      hmajor
  rw [cmp116ComplexWeakeningMultiplicitySeries]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (Summable.tsum_le_tsum
      (fun walk =>
        norm_cmp116ComplexWeakeningMultiplicityTerm_le_radialMajorant
          (multiplicity walk) (term walk) sigma R (hsigma walk))
      hnorm hmajor)

/-- At full coupling every multiplicity monomial is one. -/
theorem cmp116ComplexWeakeningMultiplicitySeries_one
    (multiplicity : Walk → Delta →₀ ℕ) (term : Walk → E) :
    cmp116ComplexWeakeningMultiplicitySeries multiplicity term (fun _ => 1) =
      ∑' walk, term walk := by
  rw [cmp116ComplexWeakeningMultiplicitySeries]
  apply tsum_congr
  intro walk
  simp [cmp116ComplexWeakeningMultiplicityMonomial]

/-- Source data for the multiplicity-aware equation-(1.11) deduction.
`baseWeight` is indexed after every finite powerset expansion, so its
summability is where the physical finite combinatorial cost must be paid. -/
structure CMP116Lemma1MultiplicityPropagatorCertificate
    (multiplicity : Walk → Delta →₀ ℕ)
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
    16 < cmp116WeakeningMultiplicityDegree (multiplicity walk) →
      delta1 *
          (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) * M ≤
        delta0 * (treeLength walk : ℝ)

namespace CMP116Lemma1MultiplicityPropagatorCertificate

variable
    {multiplicity : Walk → Delta →₀ ℕ}
    {term : Walk → E}
    {treeLength : Walk → ℕ}
    {baseWeight : Walk → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1MultiplicityPropagatorCertificate
      multiplicity term treeLength baseWeight B0 delta0 delta1 M kappa1)

include C

/-- The printed short/long split, with total multiplicity degree left as the
explicit physical source obligation. -/
theorem walkExponent_le_sixteen
    (walk : Walk) :
    kappa1 *
          (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) -
        delta0 * (treeLength walk : ℝ) ≤
      16 * kappa1 := by
  by_cases hshort :
      cmp116WeakeningMultiplicityDegree (multiplicity walk) ≤ 16
  · have hm :
        (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) ≤ 16 := by
      exact_mod_cast hshort
    have hd : 0 ≤ delta0 * (treeLength walk : ℝ) :=
      mul_nonneg C.delta0_nonneg (Nat.cast_nonneg _)
    nlinarith [C.kappa1_nonneg]
  · have hlong :
        16 < cmp116WeakeningMultiplicityDegree (multiplicity walk) := by
      omega
    have hm0 :
        0 ≤ (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) :=
      Nat.cast_nonneg _
    have hscale := mul_le_mul_of_nonneg_right C.scale_budget hm0
    have hgeom := C.long_walk_geometry walk hlong
    have habsorb :
        kappa1 *
            (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) ≤
          delta0 * (treeLength walk : ℝ) := by
      calc
        kappa1 *
              (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) ≤
            (delta1 * M) *
              (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) :=
          hscale
        _ = delta1 *
              (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) *
                M := by ring
        _ ≤ delta0 * (treeLength walk : ℝ) := hgeom
    nlinarith [C.kappa1_nonneg]

/-- One total-degree radial summand is absorbed by the source walk weight. -/
theorem radialMajorant_le
    (walk : Walk) :
    (Real.exp kappa1) ^
          cmp116WeakeningMultiplicityDegree (multiplicity walk) *
        ‖term walk‖ ≤
      Real.exp (16 * kappa1) * baseWeight walk := by
  calc
    (Real.exp kappa1) ^
            cmp116WeakeningMultiplicityDegree (multiplicity walk) *
          ‖term walk‖ ≤
        (Real.exp kappa1) ^
            cmp116WeakeningMultiplicityDegree (multiplicity walk) *
          (baseWeight walk *
            Real.exp (-(delta0 * (treeLength walk : ℝ)))) :=
      mul_le_mul_of_nonneg_left (C.source_walk_bound walk)
        (pow_nonneg (Real.exp_nonneg _) _)
    _ = baseWeight walk *
        Real.exp
          (kappa1 *
              (cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) -
            delta0 * (treeLength walk : ℝ)) := by
      rw [← Real.exp_nat_mul]
      calc
        Real.exp
              ((cmp116WeakeningMultiplicityDegree (multiplicity walk) : ℝ) *
                kappa1) *
              (baseWeight walk *
                Real.exp (-(delta0 * (treeLength walk : ℝ)))) =
            baseWeight walk *
              (Real.exp
                  ((cmp116WeakeningMultiplicityDegree
                      (multiplicity walk) : ℝ) * kappa1) *
                Real.exp (-(delta0 * (treeLength walk : ℝ)))) := by ring
        _ = baseWeight walk *
              Real.exp
                (((cmp116WeakeningMultiplicityDegree
                    (multiplicity walk) : ℝ) * kappa1) +
                  (-(delta0 * (treeLength walk : ℝ)))) := by
            rw [Real.exp_add]
        _ = baseWeight walk *
              Real.exp
                (kappa1 *
                    (cmp116WeakeningMultiplicityDegree
                      (multiplicity walk) : ℝ) -
                  delta0 * (treeLength walk : ℝ)) := by
            congr 2
            ring
    _ ≤ baseWeight walk * Real.exp (16 * kappa1) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (C.walkExponent_le_sixteen walk))
        (C.baseWeight_nonneg walk)
    _ = Real.exp (16 * kappa1) * baseWeight walk := by ring

/-- The source budget makes the total-degree radial majorant summable. -/
theorem summable_radialMajorant :
    Summable fun walk =>
      (Real.exp kappa1) ^
          cmp116WeakeningMultiplicityDegree (multiplicity walk) *
        ‖term walk‖ := by
  exact Summable.of_nonneg_of_le
    (fun walk => mul_nonneg (pow_nonneg (Real.exp_nonneg _) _)
      (norm_nonneg _))
    (fun walk => C.radialMajorant_le walk)
    (C.baseWeight_summable.mul_left (Real.exp (16 * kappa1)))

/-- The multiplicity-aware propagator is the literal complex `tsum`. -/
noncomputable def propagator
    (_C : CMP116Lemma1MultiplicityPropagatorCertificate
      multiplicity term treeLength baseWeight B0 delta0 delta1 M kappa1)
    (sigma : Delta → ℂ) : E :=
  cmp116ComplexWeakeningMultiplicitySeries multiplicity term sigma

/-- The internally constructed family recovers the unweakened walk series. -/
theorem propagator_one :
    C.propagator (fun _ => 1) = ∑' walk, term walk := by
  simpa [propagator] using
    (cmp116ComplexWeakeningMultiplicitySeries_one multiplicity term)

/-- Multiplicity-aware equation-(1.11)-shaped bound on the same polydisc. -/
theorem norm_propagator_le
    (sigma : Delta → ℂ)
    (hsigma : sigma ∈ cmp116Lemma1WeakeningPolydisc kappa1) :
    ‖C.propagator sigma‖ ≤ B0 * Real.exp (16 * kappa1) := by
  have hseries :=
    norm_cmp116ComplexWeakeningMultiplicitySeries_le_tsum_majorant
      multiplicity term sigma (Real.exp kappa1)
      (fun walk d hd => hsigma d) C.summable_radialMajorant
  have htsum :
      (∑' walk,
          (Real.exp kappa1) ^
              cmp116WeakeningMultiplicityDegree (multiplicity walk) *
            ‖term walk‖) ≤
        ∑' walk, Real.exp (16 * kappa1) * baseWeight walk :=
    Summable.tsum_le_tsum
      (fun walk => C.radialMajorant_le walk)
      C.summable_radialMajorant
      (C.baseWeight_summable.mul_left (Real.exp (16 * kappa1)))
  calc
    ‖C.propagator sigma‖ ≤
        ∑' walk,
          (Real.exp kappa1) ^
              cmp116WeakeningMultiplicityDegree (multiplicity walk) *
            ‖term walk‖ := by
      simpa [propagator] using hseries
    _ ≤ ∑' walk, Real.exp (16 * kappa1) * baseWeight walk := htsum
    _ = Real.exp (16 * kappa1) * ∑' walk, baseWeight walk :=
      tsum_mul_left
    _ ≤ Real.exp (16 * kappa1) * B0 :=
      mul_le_mul_of_nonneg_left C.baseWeight_tsum_le (Real.exp_nonneg _)
    _ = B0 * Real.exp (16 * kappa1) := by ring

end CMP116Lemma1MultiplicityPropagatorCertificate

section OperatorApplication

universe x y

variable {X : Type x} {Y : Type y}
variable [NormedAddCommGroup X] [NormedSpace ℂ X]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Operator-action form of the multiplicity-aware equation-(1.11) bound. -/
theorem CMP116Lemma1MultiplicityPropagatorCertificate.norm_propagator_apply_le
    {multiplicity : Walk → Delta →₀ ℕ}
    {term : Walk → (X →L[ℂ] Y)}
    {treeLength : Walk → ℕ}
    {baseWeight : Walk → ℝ}
    {B0 delta0 delta1 M kappa1 : ℝ}
    (C : CMP116Lemma1MultiplicityPropagatorCertificate
      multiplicity term treeLength baseWeight B0 delta0 delta1 M kappa1)
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
