/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexWeakeningCauchy
import YangMills.RG.PhysicalGaugeCovarianceLocalization

/-!
# Complex weakening of physical random-walk kernel coefficients

The CMP99 patched-walk terms are real continuous endomorphisms of the physical
one-cochain space, whereas equation (2.14) inserts complex weakening
parameters.  A full abstract complexification of the real Banach space is
neither needed nor desirable here.  The source ultimately uses kernel
coefficients, so this module probes each physical operator with canonical
Lie-coordinate basis vectors and embeds the resulting real scalar into
`Complex`.

The scalar coefficient is bounded by the operator norm with constant one.
Consequently summability of the already constructed radial physical operator
series produces the exact real majorant needed by the complex Cauchy series.
No finite-dimensional condition number or ambient cardinality appears.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

universe u v

set_option synthInstance.maxHeartbeats 800000

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Canonical real kernel coefficient of a physical one-cochain
endomorphism, with one input and one output Lie coordinate selected. -/
noncomputable def cmp116PhysicalOperatorCoefficient
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) : ℝ :=
  (T (singlePhysicalBondCochain source
      (EuclideanSpace.single input (1 : ℝ))) target) output

/-- The complex kernel coefficient used by the complex weakening series. -/
noncomputable def cmp116ComplexPhysicalOperatorCoefficient
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) : ℂ :=
  (cmp116PhysicalOperatorCoefficient T source target input output : ℂ)

/-- A canonical physical kernel coefficient is bounded by the operator norm
with constant one. -/
theorem abs_cmp116PhysicalOperatorCoefficient_le_norm
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) :
    |cmp116PhysicalOperatorCoefficient T source target input output| ≤ ‖T‖ := by
  calc
    |cmp116PhysicalOperatorCoefficient T source target input output| =
        ‖(T (singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ))) target) output‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ‖T (singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ))) target‖ :=
      PiLp.norm_apply_le _ output
    _ ≤ ‖T (singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ)))‖ :=
      PiLp.norm_apply_le _ target
    _ ≤ ‖T‖ * ‖singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ))‖ :=
      T.le_opNorm _
    _ = ‖T‖ := by
      rw [norm_singlePhysicalBondCochain, EuclideanSpace.norm_single]
      simp

/-- The norm of the complexified kernel coefficient has the same sharp
operator-norm bound. -/
theorem norm_cmp116ComplexPhysicalOperatorCoefficient_le_norm
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) :
    ‖cmp116ComplexPhysicalOperatorCoefficient
        T source target input output‖ ≤ ‖T‖ := by
  simpa [cmp116ComplexPhysicalOperatorCoefficient, Complex.norm_real,
    cmp116PhysicalOperatorCoefficient] using
    abs_cmp116PhysicalOperatorCoefficient_le_norm
      T source target input output

/-- The coefficient is bounded already by the norm of the physical output
vector at the selected target.  This sharper intermediate form preserves the
spatial decay of a fixed-rate kernel estimate; passing immediately to the
global operator norm would discard it. -/
theorem norm_cmp116ComplexPhysicalOperatorCoefficient_le_targetValue
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (T : PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) :
    ‖cmp116ComplexPhysicalOperatorCoefficient
        T source target input output‖ ≤
      ‖T (singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ))) target‖ := by
  simpa [cmp116ComplexPhysicalOperatorCoefficient,
    cmp116PhysicalOperatorCoefficient, Complex.norm_real,
    Real.norm_eq_abs] using
      (PiLp.norm_apply_le
        (T (singlePhysicalBondCochain source
          (EuclideanSpace.single input (1 : ℝ))) target) output)

/-- Summability of the radial physical operator family implies summability of
the radial complex kernel-coefficient majorant. -/
theorem summable_cmp116ComplexPhysicalCoefficient_radialMajorant
    {Δ : Type u} {ω : Type v}
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (active : ω → Finset Δ) (term : ω → PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) (R : ℝ)
    (hR : 0 ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term walk) :
    Summable fun walk =>
      R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term walk) source target input output‖ := by
  have hop : Summable fun walk =>
      R ^ (active walk).card * ‖term walk‖ := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR] using hsum.norm
  apply Summable.of_nonneg_of_le
  · intro walk
    exact mul_nonneg (pow_nonneg hR _) (norm_nonneg _)
  · intro walk
    exact mul_le_mul_of_nonneg_left
      (norm_cmp116ComplexPhysicalOperatorCoefficient_le_norm
        (term walk) source target input output)
      (pow_nonneg hR _)
  · exact hop

/-- A summable radial physical operator family directly supplies the Cauchy
boundary bound for each literal physical kernel coefficient. -/
theorem cmp116Eq214CauchyBoundaryBound_of_physicalWalkKernel
    {Δ : Type u} {ω : Type v}
    {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    {n : ℕ} (emb : Fin n ↪ Δ) (radius : Fin n → ℝ)
    (active : ω → Finset Δ) (term : ω → PhysicalEndomorphism d N Nc)
    (source target : PhysicalBond d N)
    (input output : Fin (Nc ^ 2 - 1)) (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term walk) :
    CMP116Eq214CauchyBoundaryBound n radius
      (fun z => cmp116ComplexWeakenedRandomWalkSeries active
        (fun walk => cmp116ComplexPhysicalOperatorCoefficient
          (term walk) source target input output)
        (cmp116ComplexWeakeningOfContour emb z))
      (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term walk) source target input output‖) := by
  exact cmp116Eq214CauchyBoundaryBound_of_complexWeakenedRandomWalkSeries
    emb radius active
    (fun walk => cmp116ComplexPhysicalOperatorCoefficient
      (term walk) source target input output)
    R hR hcap
    (summable_cmp116ComplexPhysicalCoefficient_radialMajorant
      active term source target input output R (zero_le_one.trans hR) hsum)

end YangMills.RG
