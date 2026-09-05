/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq3163Hprime
import YangMills.RG.BalabanCMP99SourceGeneratedMiddleSymmetry

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

/-- Symmetry of the finite-rank complement in equation (3.25).  The
`Qstar` occurring in the printed formula is the adjoint for the weighted
lattice scalar products.  The scalar relation with the counting-space
Hilbert adjoint is kept explicit; no identification of the two adjoints is
made. -/
theorem cmp99Eq325Complement_isSymmetric_of_weightedAdjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (Q : E →L[ℝ] F) (Qstar : F →L[ℝ] E)
    (G : E →L[ℝ] E) (C : F →L[ℝ] F) (s : ℝ)
    (hQ : Q = s • Qstar.adjoint)
    (hG : G.IsSymmetric) (hC : C.IsSymmetric) :
    (G.comp (Qstar.comp (C.comp (Q.comp G)))).IsSymmetric := by
  rw [hQ]
  intro x y
  change inner ℝ (G (Qstar (C (s • Qstar.adjoint (G x))))) y =
    inner ℝ x (G (Qstar (C (s • Qstar.adjoint (G y)))))
  rw [map_smul, map_smul, map_smul, inner_smul_left,
    map_smul, map_smul, map_smul, inner_smul_right]
  congr 1
  calc
    inner ℝ (G (Qstar (C (Qstar.adjoint (G x))))) y =
        inner ℝ (Qstar (C (Qstar.adjoint (G x)))) (G y) := hG _ _
    _ = inner ℝ (C (Qstar.adjoint (G x)))
        (Qstar.adjoint (G y)) :=
      (ContinuousLinearMap.adjoint_inner_right Qstar _ _).symm
    _ = inner ℝ (Qstar.adjoint (G x))
        (C (Qstar.adjoint (G y))) := hC _ _
    _ = inner ℝ (C (Qstar.adjoint (G y)))
        (Qstar.adjoint (G x)) := real_inner_comm _ _
    _ = inner ℝ (Qstar (C (Qstar.adjoint (G y)))) (G x) :=
      ContinuousLinearMap.adjoint_inner_right Qstar _ _
    _ = inner ℝ (G x) (Qstar (C (Qstar.adjoint (G y)))) :=
      real_inner_comm _ _
    _ = inner ℝ x (G (Qstar (C (Qstar.adjoint (G y))))) := hG _ _

/-- Subtracting a symmetric operator from the identity preserves
symmetry. -/
theorem cmp99Eq325Projection_isSymmetric_of_complement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (hP : P.IsSymmetric) :
    (ContinuousLinearMap.id ℝ E - P).IsSymmetric := by
  intro x y
  change inner ℝ (x - P x) y = inner ℝ x (y - P y)
  rw [inner_sub_left, inner_sub_right]
  congr 1
  exact hP x y

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
/-- The finite-rank complement in the literal source formula (3.25) is
self-adjoint in counting coordinates.  The proof uses the exact positive
spacing ratio relating the printed weighted adjoint to Lean's Hilbert
adjoint. -/
theorem cmp99SourceEq325PhysicalGaugeComplement_isSymmetric
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
    (cmp99SourceEq325PhysicalGaugeComplement hd hM Omega depth hspacing
      background budget fineSmall hsmall).IsSymmetric := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  have hterminalEq : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hterminal : 0 < T.terminalSpacing := by
    rw [hterminalEq]
    exact mul_pos (pow_pos hMpos _) hspacing
  have hQ : T.Qprime =
      (spacing ^ d / T.terminalSpacing ^ d) • T.weightedAdjoint.adjoint :=
    T.Qprime_eq_smul_weightedAdjoint_adjoint hterminal
  have hG : G.IsSymmetric :=
    cmp99SourceGeneratedPhysicalGreen_isSymmetric hd hM Omega depth hspacing
      background budget fineSmall hsmall
  have hMiddle :
      (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
        hspacing background budget fineSmall hsmall).IsSymmetric :=
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_isSymmetric hd hM
      Omega depth hspacing background budget fineSmall hsmall
  have hC : C.IsSymmetric :=
    covarianceOfIsCoerciveCLM_isSymmetric _ _ _ hMiddle
  unfold cmp99SourceEq325PhysicalGaugeComplement
  exact cmp99Eq325Complement_isSymmetric_of_weightedAdjoint
    T.Qprime T.weightedAdjoint G C
      (spacing ^ d / T.terminalSpacing ^ d) hQ hG hC

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- The literal CMP99 equation-(3.25) idempotent is an orthogonal
projection. -/
theorem cmp99SourceEq325PhysicalGaugeProjection_isSymmetric
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
    (cmp99SourceEq325PhysicalGaugeProjection hd hM Omega depth hspacing
      background budget fineSmall hsmall).IsSymmetric := by
  unfold cmp99SourceEq325PhysicalGaugeProjection
  exact cmp99Eq325Projection_isSymmetric_of_complement _
    (cmp99SourceEq325PhysicalGaugeComplement_isSymmetric hd hM Omega depth
      hspacing background budget fineSmall hsmall)

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
