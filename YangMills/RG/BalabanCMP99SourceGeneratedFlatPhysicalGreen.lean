/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
# Canonical generated flat physical Green

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

At radius zero the recursively generated Poincare error is exactly zero at
every depth.  This module uses that identity, the canonical generated spacing
and the already constructed zero-radius source budget to build the literal
physical Green internally.  Both inverse laws are inherited from the same
coercive physical precision.

No complexification, full-box inverse, regional compression or Green
transport is asserted here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The accumulated source Poincare error vanishes identically at radius
zero, at every depth and spacing. -/
@[simp] theorem cmp99SourcePoincareErrorCoeff_zero
    (d M depth : ℕ) [NeZero d] [NeZero M] (spacing : ℝ) :
    cmp99SourcePoincareErrorCoeff d M depth spacing 0 = 0 := by
  induction depth generalizing spacing with
  | zero => rfl
  | succ depth ih =>
      simp [cmp99SourcePoincareErrorCoeff,
        cmp99SourceScaledGradientStepError,
        cmp99SourceTripleHolonomyRadius,
        cmp99SourceUbarNextFineRadius_zero, ih]

/-- The canonical generated spacing is strictly positive. -/
theorem cmp99SourceGeneratedFullComplexSpacing_pos
    (M depth : ℕ) [NeZero M] :
    0 < cmp99SourceGeneratedFullComplexSpacing M depth := by
  unfold cmp99SourceGeneratedFullComplexSpacing
  positivity

/-- Literal generated physical Green at the flat background, canonical
spacing and zero source radius.  Coercivity and every small-field datum are
constructed internally. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalGreen
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  let spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
  cmp99SourceGeneratedPhysicalGreen hd hM Omega depth
    (cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 1))
    (cmp99SourceFlatGaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget (d := d) (M := M) (Nc := Nc)
      (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp [spacing])

/-- The canonical flat precision followed by its internally generated Green
is the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalPrecision_comp_green
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalPrecision hd hM Omega depth
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1))).comp
        (cmp99SourceGeneratedFlatPhysicalGreen hd hM Omega depth) =
      ContinuousLinearMap.id ℝ _ := by
  exact cmp99SourceGeneratedPhysicalPrecision_comp_green hd hM Omega depth
    (cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 1))
    (cmp99SourceFlatGaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget (d := d) (M := M) (Nc := Nc)
      (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp)

/-- The internally generated flat Green followed by the same canonical flat
precision is the identity. -/
theorem cmp99SourceGeneratedFlatPhysicalGreen_comp_precision
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) :
    (cmp99SourceGeneratedFlatPhysicalGreen hd hM Omega depth).comp
        (cmp99SourceGeneratedFlatPhysicalPrecision hd hM Omega depth
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1))) =
      ContinuousLinearMap.id ℝ _ := by
  exact cmp99SourceGeneratedPhysicalGreen_comp_precision hd hM Omega depth
    (cmp99SourceGeneratedFullComplexSpacing_pos M (depth + 1))
    (cmp99SourceFlatGaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget (d := d) (M := M) (Nc := Nc)
      (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small
    (by simp)

end

end YangMills.RG
