/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq3163Hprime

/-!
# The literal CMP99 equation-(3.25) gauge projection

On printed p. 394, CMP99 defines the zero-cochain operator

`R = I - G' Q'^* (Q' G'^2 Q'^*)^-1 Q' G'`.

This file constructs that formula from the source-generated regional Green,
the physical weighted adjoint of the complete `Q'` tower, and the generated
coarse covariance.  The inverse identities already proved for
`Q' G'^2 Q'^*` imply that the complementary term is an idempotent.  Hence
`R` is an idempotent, and it satisfies the exact normal equation

`Q' G' R = 0`.

Honest scope: equation (3.124), `R D^* G Q^* = 0`, is a further identity for
the one-cochain background problem.  CMP99 proves it by a Gaussian symmetry
argument around equations (3.121)--(3.125); it is not inferred here merely
from idempotence of `R`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Algebraic core of equation (3.25): if `C` is a right inverse of
`Q G² Qstar`, then `G Qstar C Q G` is idempotent. -/
theorem cmp99Eq325Complement_comp_self_of_middle_comp_inverse
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] F) (Qstar : F →L[ℝ] E)
    (G : E →L[ℝ] E) (C : F →L[ℝ] F)
    (hMC : (Q.comp (G.comp (G.comp Qstar))).comp C =
      ContinuousLinearMap.id ℝ F) :
    let P := G.comp (Qstar.comp (C.comp (Q.comp G)))
    P.comp P = P := by
  dsimp only
  calc
    (G.comp (Qstar.comp (C.comp (Q.comp G)))).comp
        (G.comp (Qstar.comp (C.comp (Q.comp G)))) =
      G.comp (Qstar.comp (C.comp
        (((Q.comp (G.comp (G.comp Qstar))).comp C).comp
          (Q.comp G)))) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = G.comp (Qstar.comp (C.comp (Q.comp G))) := by
      rw [hMC, ContinuousLinearMap.id_comp]

/-- The complement of any idempotent is idempotent. -/
theorem cmp99Eq325Projection_comp_self_of_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (hP : P.comp P = P) :
    (ContinuousLinearMap.id ℝ E - P).comp
        (ContinuousLinearMap.id ℝ E - P) =
      ContinuousLinearMap.id ℝ E - P := by
  ext x
  have hPx := congrArg (fun T : E →L[ℝ] E => T x) hP
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at hPx ⊢
  rw [map_sub, hPx]
  module

/-- The normal equation `Q G (I - G Qstar C Q G) = 0`. -/
theorem cmp99Eq325_QG_comp_projection_eq_zero_of_middle_comp_inverse
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] F) (Qstar : F →L[ℝ] E)
    (G : E →L[ℝ] E) (C : F →L[ℝ] F)
    (hMC : (Q.comp (G.comp (G.comp Qstar))).comp C =
      ContinuousLinearMap.id ℝ F) :
    Q.comp (G.comp (ContinuousLinearMap.id ℝ E -
      G.comp (Qstar.comp (C.comp (Q.comp G))))) = 0 := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.comp_sub]
  change Q.comp G -
      ((Q.comp (G.comp (G.comp Qstar))).comp C).comp (Q.comp G) = 0
  rw [hMC, ContinuousLinearMap.id_comp]
  module

/-- The complementary finite-rank term subtracted from the identity in
CMP99 equation (3.25). -/
noncomputable def cmp99SourceEq325PhysicalGaugeComplement
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  exact G.comp (T.weightedAdjoint.comp (C.comp (T.Qprime.comp G)))

/-- Literal CMP99 equation-(3.25) projection. -/
noncomputable def cmp99SourceEq325PhysicalGaugeProjection
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  ContinuousLinearMap.id ℝ _ -
    cmp99SourceEq325PhysicalGaugeComplement hd hM Omega depth hspacing
      background budget fineSmall hsmall

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- The complementary term in (3.25) is an idempotent. -/
theorem cmp99SourceEq325PhysicalGaugeComplement_comp_self
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let P := cmp99SourceEq325PhysicalGaugeComplement hd hM Omega depth
      hspacing background budget fineSmall hsmall
    P.comp P = P := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM
    Omega depth hspacing background budget fineSmall hsmall
  have hMiddle : Middle = T.Qprime.comp (G.comp (G.comp T.weightedAdjoint)) :=
    rfl
  have hMC : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp hd hM Omega depth
      hspacing background budget fineSmall hsmall
  unfold cmp99SourceEq325PhysicalGaugeComplement
  apply cmp99Eq325Complement_comp_self_of_middle_comp_inverse
  simpa only [hMiddle] using hMC

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- The operator in CMP99 equation (3.25) is an idempotent projection. -/
theorem cmp99SourceEq325PhysicalGaugeProjection_comp_self
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let R := cmp99SourceEq325PhysicalGaugeProjection hd hM Omega depth
      hspacing background budget fineSmall hsmall
    R.comp R = R := by
  dsimp only
  let P := cmp99SourceEq325PhysicalGaugeComplement hd hM Omega depth
    hspacing background budget fineSmall hsmall
  have hP : P.comp P = P :=
    cmp99SourceEq325PhysicalGaugeComplement_comp_self hd hM Omega depth
      hspacing background budget fineSmall hsmall
  unfold cmp99SourceEq325PhysicalGaugeProjection
  exact cmp99Eq325Projection_comp_self_of_complement P hP

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- Exact normal equation for the source projection:
`Q' G' R = 0`. -/
theorem cmp99SourceEq325_Qprime_comp_green_comp_projection_eq_zero
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
      background budget fineSmall hsmall
    T.Qprime.comp (G.comp
      (cmp99SourceEq325PhysicalGaugeProjection hd hM Omega depth hspacing
        background budget fineSmall hsmall)) = 0 := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM
    Omega depth hspacing background budget fineSmall hsmall
  have hMiddle : Middle = T.Qprime.comp (G.comp (G.comp T.weightedAdjoint)) :=
    rfl
  have hMC : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp hd hM Omega depth
      hspacing background budget fineSmall hsmall
  unfold cmp99SourceEq325PhysicalGaugeProjection
  unfold cmp99SourceEq325PhysicalGaugeComplement
  apply cmp99Eq325_QG_comp_projection_eq_zero_of_middle_comp_inverse
  simpa only [hMiddle] using hMC

end

end YangMills.RG
