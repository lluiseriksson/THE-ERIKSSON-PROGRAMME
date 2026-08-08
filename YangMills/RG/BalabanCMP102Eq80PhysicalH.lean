/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80GlobalPotential
import YangMills.RG.BalabanCMP99SourceEq3126PhysicalH

/-!
# CMP102 equation (80) with the unprojected equation-(3.126) auxiliary

CMP102 equation (80) applies the background minimizer `H` to the coarse
corrections `D(A')` and `D₃(A')`, producing fine one-cochains.  Consequently
the source formula is rectangular: the field and the output of `H` are fine,
whereas the input of `H` is coarse.  This file consumes the literal CMP99
equation-(3.126) operator

`H = G Q^* (Q G Q^*)^-1`

inside the rectangular equation-(80) functional.  At this checkpoint the
operator uses the unprojected CMP116 precision documented in
`BalabanCMP99SourceEq3126PhysicalH`; it is therefore an auxiliary consumer,
not yet the full source background minimizer.  The block response
`Q (H (D A')) = D A'` is generated internally from `Q H = 1`.

Honest scope: `D`, `D₃`, `V₀`, `Δπ`, and `J` remain the separately visible
CMP102 source ingredients.  The projected mass `D R D^*`, the additional
`Delta'_pi` term, and equation (3.124) remain absent from this auxiliary.
This file does not identify localized random-walk expansions with a CMP116
activity and does not claim the gauge equation `R D^* H = 0`.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- CMP102 equation (80), with its background map fixed to the unprojected
one-scale realization of the equation-(3.126) algebraic formula. -/
noncomputable def cmp102Eq80PhysicalGlobalPotential
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J A' : FinePhysicalOneCochain d L N' Nc) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget) Δπ J A'

/-- The physical background responds to a coarse correction exactly: applying
the literal block constraint after `H` returns the correction. -/
theorem flatBlockConstraint_apply_physicalH_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (B : CoarsePhysicalOneCochain d N' Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget B) = B := by
  have h := congrArg
    (fun T : CoarsePhysicalOneCochain d N' Nc →L[ℝ]
        CoarsePhysicalOneCochain d N' Nc => T B)
    (flatBlockConstraint_comp_cmp99SourceEq3126PhysicalH_eq_id
      U ha hP hε hsmall hbudget)
  simpa using h

/-- In particular, the background inserted into the first nonlinear CMP102
correction has the exact required coarse block value. -/
theorem flatBlockConstraint_apply_physicalH_D
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (A' : FinePhysicalOneCochain d L N' Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget (D A')) =
      D A' :=
  flatBlockConstraint_apply_physicalH_apply
    U ha hP hε hsmall hbudget (D A')

/-- The component normalizations imply normalization of the physical
equation-(80) potential. -/
theorem cmp102Eq80PhysicalGlobalPotential_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80PhysicalGlobalPotential U ha hP hε hsmall hbudget
      D D₃ V₀ Δπ J 0 = 0 := by
  exact cmp102Eq80GlobalPotential_zero D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)
    Δπ J hD0 hD₃0 hV₀0

/-- Zero derivative at the origin for the physical rectangular
equation-(80) functional. -/
theorem cmp102Eq80PhysicalGlobalPotential_hasFDerivAt_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (D' : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ]
        CoarsePhysicalOneCochain d N' Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (cmp102Eq80PhysicalGlobalPotential U ha hP hε hsmall hbudget
        D D₃ V₀ Δπ J)
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ] ℝ) 0 := by
  exact cmp102Eq80GlobalPotential_hasFDerivAt_zero D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)
    Δπ J D' hD0 hD₃0 hD hD₃ hV₀

/-- `C²` regularity propagates through the physical equation-(3.126)
background map. -/
theorem contDiff_two_cmp102Eq80PhysicalGlobalPotential
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 2
      (cmp102Eq80PhysicalGlobalPotential U ha hP hε hsmall hbudget
        D D₃ V₀ Δπ J) := by
  exact contDiff_two_cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)
    Δπ J hD hD₃ hV₀

/-- Smooth regularity propagates through the physical equation-(3.126)
background map. -/
theorem contDiff_top_cmp102Eq80PhysicalGlobalPotential
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤
      (cmp102Eq80PhysicalGlobalPotential U ha hP hε hsmall hbudget
        D D₃ V₀ Δπ J) := by
  exact contDiff_top_cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)
    Δπ J hD hD₃ hV₀

end

end YangMills.RG
