/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq120SourceCurve

/-!
# Four-line CMP98 (124) decomposition in the source right frame

The curve reconstructed from (118)--(120) selects the outer operator
`g(ad (-Y))`.  This file performs the same exact `operator - 1` regrouping
as the older left-frame bridge, but now in that source-selected right frame.
No identification between the two frames is assumed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- One local source transported by the outer operator forced by the
right-trivialized source curve. -/
def cmp98Eq119RightOuterLocalTransport
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Yx := nearLog (cmp98UbarAmbientDeviationMatrix U b x 0)
  let D := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  cmp98GAd (-(cmp98UbarLogAverage U b 0))
    (cmp98GAdInv Yx (Matrix.conjTranspose D * H * D))

/-- Entrance `operator - 1` correction in the source right frame. -/
def cmp98Eq119RightEntranceOperatorMinusId
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119RightOuterLocalTransport U A b x
      (cmp98Eq124EntrancePrefixRightVariation U A b x) -
    cmp98Eq124EntrancePrefixRightVariation U A b x

/-- Middle `operator - 1` correction in the source right frame. -/
def cmp98Eq119RightMiddleOperatorMinusId
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119RightOuterLocalTransport U A b x
      (cmp98Eq124MiddlePrefixRightVariation U A b x) -
    cmp98Eq124MiddlePrefixRightVariation U A b x

/-- Local four-source average regrouped in the source right frame. -/
def cmp98Eq119RightRegroupedFourSourcePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      (cmp98Eq124EntrancePrefixRightVariation U A b x +
        cmp98Eq124MiddlePrefixRightVariation U A b x +
        cmp98Eq119RightEntranceOperatorMinusId U A b x +
        cmp98Eq119RightMiddleOperatorMinusId U A b x +
        cmp98Eq119RightOuterLocalTransport U A b x
          (cmp98Eq124ExitPrefixRightVariation U A b x) +
        cmp98Eq119RightOuterLocalTransport U A b x
          (cmp98Eq124CoarsePrefixRightVariation U A b x))

/-- Exact operator-minus-identity decomposition of the right four-source
term. -/
theorem cmp98Eq119RightFourSourcePhysicalVariation_eq_regrouped
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119RightFourSourcePhysicalVariation U A b =
      cmp98Eq119RightRegroupedFourSourcePhysicalVariation U A b := by
  unfold cmp98Eq119RightFourSourcePhysicalVariation
    cmp98Eq124FourSourceGAdInvAverage
    cmp98Eq119RightRegroupedFourSourcePhysicalVariation
  rw [map_smul]
  apply congrArg (((M : ℝ) ^ d)⁻¹ • ·)
  calc
    cmp98GAd (-(cmp98UbarLogAverage U b 0))
        (∑ x ∈ blockOf M N' b.1,
          cmp98Eq124LocalFourSourceGAdInvVariation U A b x) =
      ∑ x ∈ blockOf M N' b.1,
        cmp98GAd (-(cmp98UbarLogAverage U b 0))
          (cmp98Eq124LocalFourSourceGAdInvVariation U A b x) := by
        induction blockOf M N' b.1 using Finset.induction_on with
        | empty => exact
            (cmp98GAd (-(cmp98UbarLogAverage U b 0))).map_zero
        | @insert x s hx ih =>
            simp only [Finset.sum_insert, hx, not_false_eq_true, map_add]
            rw [ih]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [cmp98Eq124LocalFourSourceGAdInvVariation, map_add,
        cmp98Eq119RightOuterLocalTransport,
        cmp98Eq119RightEntranceOperatorMinusId,
        cmp98Eq119RightMiddleOperatorMinusId]
      abel

/-- Four source groups of (124) in the right frame fixed by (118)--(120). -/
def cmp98Eq124RightPrintedFourLinePhysicalVariation
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf M N' b.1,
        (cmp98Eq124MiddlePrefixRightVariation U A b x +
          cmp98Eq119RightEntranceOperatorMinusId U A b x +
          cmp98Eq119RightMiddleOperatorMinusId U A b x +
          (cmp98Eq119RightOuterLocalTransport U A b x
              (cmp98Eq124ExitPrefixRightVariation U A b x) -
            cmp98Eq124ExitPrefixRightVariation U A b x) +
          cmp98Eq119RightOuterLocalTransport U A b x
            (cmp98Eq124CoarsePrefixRightVariation U A b x)) +
    cmp98Eq119DirectCoarseTransportedVariation U A b

/-- Exact passage `(119)+(120) → (124)` in the source-selected right frame. -/
theorem cmp98Eq120RightAssembledPhysicalVariation_eq_fourLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq120RightAssembledPhysicalVariation U A b =
      cmp98Eq124RightPrintedFourLinePhysicalVariation U A b := by
  unfold cmp98Eq120RightAssembledPhysicalVariation
  rw [cmp98Eq119RightFourSourcePhysicalVariation_eq_regrouped]
  unfold cmp98Eq119RightRegroupedFourSourcePhysicalVariation
    cmp98Eq120PhysicalEndpointCorrection
    cmp98Eq124RightPrintedFourLinePhysicalVariation
  let w : ℝ := ((M : ℝ) ^ d)⁻¹
  let direct : Matrix (Fin Nc) (Fin Nc) ℂ :=
    cmp98Eq119DirectCoarseTransportedVariation U A b
  let localTerm : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    cmp98Eq124EntrancePrefixRightVariation U A b x +
      cmp98Eq124MiddlePrefixRightVariation U A b x +
      cmp98Eq119RightEntranceOperatorMinusId U A b x +
      cmp98Eq119RightMiddleOperatorMinusId U A b x +
      cmp98Eq119RightOuterLocalTransport U A b x
        (cmp98Eq124ExitPrefixRightVariation U A b x) +
      cmp98Eq119RightOuterLocalTransport U A b x
        (cmp98Eq124CoarsePrefixRightVariation U A b x)
  let endpoint : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    0 - cmp98Eq124EntrancePrefixRightVariation U A b x -
      cmp98Eq124ExitPrefixRightVariation U A b x
  let printed : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ := fun x =>
    cmp98Eq124MiddlePrefixRightVariation U A b x +
      cmp98Eq119RightEntranceOperatorMinusId U A b x +
      cmp98Eq119RightMiddleOperatorMinusId U A b x +
      (cmp98Eq119RightOuterLocalTransport U A b x
          (cmp98Eq124ExitPrefixRightVariation U A b x) -
        cmp98Eq124ExitPrefixRightVariation U A b x) +
      cmp98Eq119RightOuterLocalTransport U A b x
        (cmp98Eq124CoarsePrefixRightVariation U A b x)
  change w • (∑ x ∈ blockOf M N' b.1, localTerm x) + direct +
      w • (∑ x ∈ blockOf M N' b.1, endpoint x) =
    w • (∑ x ∈ blockOf M N' b.1, printed x) + direct
  have hpoint : ∀ x : FinBox d (M * N'),
      localTerm x + endpoint x = printed x := by
    intro x
    dsimp only [localTerm, endpoint, printed]
    abel
  have hsum :
      (∑ x ∈ blockOf M N' b.1, localTerm x) +
          (∑ x ∈ blockOf M N' b.1, endpoint x) =
        ∑ x ∈ blockOf M N' b.1, printed x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  have hsmul :
      w • ((∑ x ∈ blockOf M N' b.1, localTerm x) +
          (∑ x ∈ blockOf M N' b.1, endpoint x)) =
        w • (∑ x ∈ blockOf M N' b.1, localTerm x) +
          w • (∑ x ∈ blockOf M N' b.1, endpoint x) := by
    ext i j
    simp [mul_add]
  calc
    w • (∑ x ∈ blockOf M N' b.1, localTerm x) + direct +
        w • (∑ x ∈ blockOf M N' b.1, endpoint x) =
      w • (∑ x ∈ blockOf M N' b.1, localTerm x) +
          w • (∑ x ∈ blockOf M N' b.1, endpoint x) + direct := by
            abel
    _ = w • ((∑ x ∈ blockOf M N' b.1, localTerm x) +
        (∑ x ∈ blockOf M N' b.1, endpoint x)) + direct := by
          exact congrArg (fun z => z + direct) hsmul.symm
    _ = w • (∑ x ∈ blockOf M N' b.1, printed x) + direct := by
      rw [hsum]

/-- Terminal source-curve form of the four lines in (124). -/
theorem deriv_cmp98Eq120SourceCurve_zero_eq_fourLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hthird : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3) :
    deriv (cmp98Eq120SourceCurve U A b) 0 =
      cmp98Eq124RightPrintedFourLinePhysicalVariation U A b := by
  rw [deriv_cmp98Eq120SourceCurve_zero U A b hthird,
    cmp98Eq120RightAssembledPhysicalVariation_eq_fourLine]

end

end YangMills.RG
