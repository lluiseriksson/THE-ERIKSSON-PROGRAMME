/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointSmooth
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Implicit-function package for the intrinsic CMP102 correction

The physical correction satisfies the certificate-free equation

`D - C_intrinsic(A - H D) = 0`.

This file separates the functional-analytic implicit-function step from the
remaining source estimate.  A strict norm bound on the *actual vertical
Fréchet derivative* makes `I - ∂_D T` invertible by the Neumann theorem.
Joint source-specific smoothness then supplies Mathlib's complete
`IsContDiffImplicitAt` package.  No regularity of a selected correction and
no regularity of scalar chart certificates is assumed.

The vertical derivative bound is generated here from the physical Banach
certificate and the two-field CMP102 estimate.  Together with continuity of
the selected fixed point this removes the legacy regularity premise from the
radial decomposition.
-/

open Function
open Filter
open scoped Topology

/-- A continuous linear perturbation of the identity with norm below one is
bijective. -/
theorem continuousLinearMap_one_sub_bijective_of_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (hL : ‖L‖ < 1) :
    Function.Bijective ((1 : E →L[ℝ] E) - L) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_one_sub_of_norm_lt_one hL)

/-- General fixed-point form of the smooth implicit-function theorem. -/
theorem isContDiffImplicitAt_fixedPoint_of_vertical_norm_lt_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : WithTop ℕ∞}
    (T : E × F → F) (T' : E × F →L[ℝ] F) (a : E × F)
    (hTderiv : HasFDerivAt T T' a)
    (hTsmooth : ContDiffAt ℝ n T a)
    (hvertical :
      ‖T'.comp (ContinuousLinearMap.inr ℝ E F)‖ < 1)
    (hn : n ≠ 0) :
    IsContDiffImplicitAt n
      (fun p : E × F => p.2 - T p)
      (ContinuousLinearMap.snd ℝ E F - T') a := by
  refine ⟨?_, ?_, ?_, hn⟩
  · exact hasFDerivAt_snd.sub hTderiv
  · exact contDiffAt_snd.sub hTsmooth
  · have hunit :
        Function.Bijective
          ((1 : F →L[ℝ] F) -
            T'.comp (ContinuousLinearMap.inr ℝ E F)) :=
      continuousLinearMap_one_sub_bijective_of_norm_lt_one _ hvertical
    simpa [ContinuousLinearMap.sub_comp] using hunit

/-- A Lipschitz estimate on a positive closed ball controls the derivative
also at boundary points, provided the derivative is continuous there.  The
boundary case is obtained by approximation from the open ball. -/
theorem norm_fderiv_le_of_lipschitzOn_closedBall
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) {ρ : ℝ} {K : NNReal}
    (hρ : 0 < ρ) (hx : ‖x‖ ≤ ρ)
    (hsmooth : ContDiffAt ℝ 1 f x)
    (hlip : LipschitzOnWith K f (Metric.closedBall 0 ρ)) :
    ‖fderiv ℝ f x‖ ≤ K := by
  by_cases hx' : ‖x‖ < ρ
  · exact norm_fderiv_le_of_lipschitzOn ℝ
      (Metric.closedBall_mem_nhds_of_mem (by
        simpa [Metric.mem_ball] using hx'))
      hlip
  · have hxball : x ∈ Metric.closedBall (0 : E) ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hxclosure : x ∈ closure (Metric.ball (0 : E) ρ) := by
      rw [closure_ball 0 hρ.ne']
      exact hxball
    have hcont :
        ContinuousAt (fun y : E => ‖fderiv ℝ f y‖) x :=
      continuous_norm.continuousAt.comp
        (hsmooth.continuousAt_fderiv (by decide))
    by_contra hnot
    have hgt : (K : ℝ) < ‖fderiv ℝ f x‖ := lt_of_not_ge hnot
    have hnh :
        {y : E | (K : ℝ) < ‖fderiv ℝ f y‖} ∈ 𝓝 x :=
      hcont (Ioi_mem_nhds hgt)
    obtain ⟨y, hygt, hyball⟩ :=
      (mem_closure_iff_nhds.mp hxclosure) _ hnh
    have hyle :
        ‖fderiv ℝ f y‖ ≤ K :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (Metric.closedBall_mem_nhds_of_mem hyball) hlip
    exact (not_lt_of_ge hyle) hygt

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The certificate-free implicit equation for the physical CMP102
background correction. -/
noncomputable def cmp102IntrinsicPhysicalBackgroundCorrectionEquation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (p : FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  p.2 - cmp102IntrinsicPhysicalBackgroundCorrectionMap
    U ha hP hε hsmall hbudget p.1 p.2

set_option maxHeartbeats 10000000 in
/-- A source chart produces the literal inner Mercator-domain condition of
the intrinsic correction at its physical field. -/
theorem CMP102PhysicalNonlinearChartBudget.intrinsic_local
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (X : PhysicalGaugeOneCochain d (L * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U X) :
    ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM X)‖ < 1 := by
  have hone : |(1 : ℝ)| < B.radius := by
    simpa using B.one_lt_radius
  intro b x hx
  have heq :
      cmp98UbarAmbientDeviationMatrix U b x
          (cmp102PhysicalCochainToAmbientCLM X) =
        (cmp98PhysicalUbarRelativeSUN U X b x 1 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1 := by
    rw [cmp102PhysicalCochainToAmbientCLM_apply]
    have hline :=
      cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one
        U X b x 1
    have hone' :
        (1 : ℝ) • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) =
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) :=
      one_smul ℝ _
    rw [hone'] at hline
    exact hline
  rw [heq]
  exact B.near b 1 hone x hx

set_option maxHeartbeats 10000000 in
/-- A source chart also produces the literal final relative Mercator-domain
condition of the intrinsic correction. -/
theorem CMP102PhysicalNonlinearChartBudget.intrinsic_relative
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (X : PhysicalGaugeOneCochain d (L * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U X) :
    ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM X) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (L * N') Nc) b - 1‖ < 1 := by
  have hone : |(1 : ℝ)| < B.radius := by
    simpa using B.one_lt_radius
  intro b
  have hEq :
      cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM X) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (L * N') Nc) b - 1 =
        cmp98Eq119NonlinearRelativeDeviation U X b 1 := by
    unfold cmp98Eq119NonlinearRelativeDeviation
    have hblock := cmp102AmbientNonlinearBlock_physicalLine_eq U X b 1
    have hone' :
        (1 : ℝ) • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) =
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent X) :=
      one_smul ℝ _
    rw [hone'] at hblock
    rw [cmp102PhysicalCochainToAmbientCLM_apply, hblock]
    rw [cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U X 0 b]
  rw [hEq]
  rw [cmp98Eq119NonlinearRelativeDeviation_eq_relativeSUN_sub_one
    U X b 1 (B.near b 1 hone) (B.noWinding b 1 hone)
      (B.near b 0 B.zero_mem) (B.noWinding b 0 B.zero_mem)]
  exact B.relativeNear b 1 hone

set_option maxHeartbeats 10000000 in
/-- The intrinsic fixed-point map inherits the already constructed physical
contraction estimate on every certified closed ball. -/
theorem lipschitzOnWith_cmp102IntrinsicPhysicalBackgroundCorrectionMap
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s) :
    LipschitzOnWith ⟨B.contractionRate, B.contractionRate_nonneg⟩
      (cmp102IntrinsicPhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A)
      (Metric.closedBall 0 ρ) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro D hD E hE
  have hD' : ‖D‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hD
  have hE' : ‖E‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hE
  let BD := B.chartBudget D hD'
  let BE := B.chartBudget E hE'
  have hphysical :=
    cmp102PhysicalBackgroundCorrectionSupNorm_sub_le
      U ha hP hε hsmall hbudget A
      (physicalGaugeOneCochainSupEquiv.symm D)
      (physicalGaugeOneCochainSupEquiv.symm E)
      BD BE r s
      (by simpa [BD] using B.localRadius_eq D hD')
      (by simpa [BE] using B.localRadius_eq E hE')
      (by simpa [BD] using B.relativeRadius_eq D hD')
      (by simpa [BE] using B.relativeRadius_eq E hE')
  have hright :
      cmp102PhysicalCorrectionSupNorm
          (physicalGaugeOneCochainSupEquiv.symm E -
            physicalGaugeOneCochainSupEquiv.symm D) =
        dist D E := by
    rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm,
      map_sub]
    simpa [dist_eq_norm] using norm_sub_rev E D
  rw [hright] at hphysical
  have hBD :
      cmp102PhysicalNonlinearCorrectionOfBudget U
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
            (physicalGaugeOneCochainSupEquiv.symm D)) BD =
        cmp102IntrinsicPhysicalNonlinearCorrection U
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
            (physicalGaugeOneCochainSupEquiv.symm D)) := by
    apply cmp102PhysicalNonlinearCorrectionOfBudget_eq_intrinsic
    intro b x hx
    exact (BD.base b x hx).trans_lt (by norm_num)
  have hBE :
      cmp102PhysicalNonlinearCorrectionOfBudget U
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
            (physicalGaugeOneCochainSupEquiv.symm E)) BE =
        cmp102IntrinsicPhysicalNonlinearCorrection U
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
            (physicalGaugeOneCochainSupEquiv.symm E)) := by
    apply cmp102PhysicalNonlinearCorrectionOfBudget_eq_intrinsic
    intro b x hx
    exact (BE.base b x hx).trans_lt (by norm_num)
  rw [hBD, hBE] at hphysical
  change
    dist
        (cmp102IntrinsicPhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A D)
        (cmp102IntrinsicPhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A E) ≤
      B.contractionRate * dist D E
  rw [dist_eq_norm]
  unfold cmp102IntrinsicPhysicalBackgroundCorrectionMap
  rw [← map_sub,
    norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  simpa [
    CMP102PhysicalBackgroundCorrectionBallData.contractionRate] using
      hphysical

set_option maxHeartbeats 10000000 in
/-- The physical contraction estimate controls the actual vertical
Fréchet derivative, including when the point lies on the boundary of the
certified ball. -/
theorem
    norm_cmp102IntrinsicPhysicalBackgroundCorrectionMap_verticalFDeriv_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (hρ : 0 < ρ)
    (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1) :
    ‖(fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D)).comp
        (ContinuousLinearMap.inr ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc))‖ ≤
      B.contractionRate := by
  let T := fun p :
      FinePhysicalOneCochain d L N' Nc ×
        PhysicalGaugeOneCochainSup d N' Nc =>
    cmp102IntrinsicPhysicalBackgroundCorrectionMap
      U ha hP hε hsmall hbudget p.1 p.2
  let slice := fun E : PhysicalGaugeOneCochainSup d N' Nc => T (A, E)
  have hjoint : ContDiffAt ℝ ⊤ T (A, D) :=
    contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionMap_uncurry
      U ha hP hε hsmall hbudget A D hlocal hrelative
  have hpath :
      HasFDerivAt
        (fun E : PhysicalGaugeOneCochainSup d N' Nc => (A, E))
        (ContinuousLinearMap.inr ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc)) D :=
    (hasFDerivAt_const (x := D) A).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := D))
  have hsliceDeriv :
      HasFDerivAt slice
        ((fderiv ℝ T (A, D)).comp
          (ContinuousLinearMap.inr ℝ
            (FinePhysicalOneCochain d L N' Nc)
            (PhysicalGaugeOneCochainSup d N' Nc))) D := by
    exact
      (hjoint.differentiableAt (by decide)).hasFDerivAt.comp D hpath
  have hsliceSmooth : ContDiffAt ℝ 1 slice D := by
    have hpathSmooth :
        ContDiffAt ℝ 1
          (fun E : PhysicalGaugeOneCochainSup d N' Nc => (A, E)) D :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hjoint.of_le le_top).comp D hpathSmooth
  have hsliceBound :
      ‖fderiv ℝ slice D‖ ≤
        (⟨B.contractionRate, B.contractionRate_nonneg⟩ : NNReal) :=
    norm_fderiv_le_of_lipschitzOn_closedBall
      slice D hρ hD hsliceSmooth
        (lipschitzOnWith_cmp102IntrinsicPhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s B)
  rw [hsliceDeriv.fderiv] at hsliceBound
  simpa [T, slice] using hsliceBound

/-- On the literal open Mercator domain, a strict bound on the actual
vertical derivative constructs the complete `C²` implicit-function datum. -/
theorem
    isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1)
    (hvertical :
      ‖(fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D)).comp
        (ContinuousLinearMap.inr ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc))‖ < 1) :
    IsContDiffImplicitAt 2
      (cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget)
      (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc) -
        fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D))
      (A, D) := by
  let T := fun p :
      FinePhysicalOneCochain d L N' Nc ×
        PhysicalGaugeOneCochainSup d N' Nc =>
    cmp102IntrinsicPhysicalBackgroundCorrectionMap
      U ha hP hε hsmall hbudget p.1 p.2
  have hTtop : ContDiffAt ℝ ⊤ T (A, D) :=
    contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionMap_uncurry
      U ha hP hε hsmall hbudget A D hlocal hrelative
  have hT2 : ContDiffAt ℝ 2 T (A, D) :=
    hTtop.of_le le_top
  have hTderiv :
      HasFDerivAt T (fderiv ℝ T (A, D)) (A, D) :=
    hT2.differentiableAt (by decide) |>.hasFDerivAt
  simpa [cmp102IntrinsicPhysicalBackgroundCorrectionEquation, T] using
    isContDiffImplicitAt_fixedPoint_of_vertical_norm_lt_one
      T (fderiv ℝ T (A, D)) (A, D)
      hTderiv hT2 hvertical (by decide)

/-- Smooth (`C∞`) version of the intrinsic implicit-function package. -/
theorem
    isContDiffImplicitAt_top_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1)
    (hvertical :
      ‖(fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D)).comp
        (ContinuousLinearMap.inr ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc))‖ < 1) :
    IsContDiffImplicitAt ⊤
      (cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget)
      (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc) -
        fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D))
      (A, D) := by
  let T := fun p :
      FinePhysicalOneCochain d L N' Nc ×
        PhysicalGaugeOneCochainSup d N' Nc =>
    cmp102IntrinsicPhysicalBackgroundCorrectionMap
      U ha hP hε hsmall hbudget p.1 p.2
  have hTtop : ContDiffAt ℝ ⊤ T (A, D) :=
    contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionMap_uncurry
      U ha hP hε hsmall hbudget A D hlocal hrelative
  have hTderiv :
      HasFDerivAt T (fderiv ℝ T (A, D)) (A, D) :=
    (hTtop.differentiableAt (by simp)).hasFDerivAt
  simpa [cmp102IntrinsicPhysicalBackgroundCorrectionEquation, T] using
    isContDiffImplicitAt_fixedPoint_of_vertical_norm_lt_one
      T (fderiv ℝ T (A, D)) (A, D)
      hTderiv hTtop hvertical (by simp)

/-- The physical Banach certificate itself discharges the vertical
invertibility requirement.  No derivative bound is supplied by the caller. -/
theorem
    isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation_of_ballData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (hρ : 0 < ρ) (hcontract : B.contractionRate < 1)
    (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1) :
    IsContDiffImplicitAt 2
      (cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget)
      (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc) -
        fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D))
      (A, D) := by
  apply
    isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
      U ha hP hε hsmall hbudget A D hlocal hrelative
  exact
    (norm_cmp102IntrinsicPhysicalBackgroundCorrectionMap_verticalFDeriv_le
      U ha hP hε hsmall hbudget A ρ r s B hρ D hD hlocal hrelative
    ).trans_lt hcontract

/-- **Fully certificate-generated implicit-function datum.**  The physical
ball certificate supplies both literal Mercator-domain conditions as well
as the vertical contraction estimate. -/
theorem
    isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation_of_generatedBallData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (hρ : 0 < ρ) (hcontract : B.contractionRate < 1)
    (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ) :
    IsContDiffImplicitAt 2
      (cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget)
      (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc) -
        fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D))
      (A, D) := by
  let X :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
      (physicalGaugeOneCochainSupEquiv.symm D)
  let BD := B.chartBudget D hD
  have hlocal :
      ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x
          (cmp102PhysicalCochainToAmbientCLM
            (cmp102PhysicalBackgroundShiftCLM
              U ha hP hε hsmall hbudget (A, D)))‖ < 1 := by
    simpa only [cmp102PhysicalBackgroundShiftCLM_apply] using
      (BD.intrinsic_local U X)
  have hrelative :
      ∀ b : PhysicalBond d N',
        ‖cmp102AmbientNonlinearBlock U b
              (cmp102PhysicalCochainToAmbientCLM
                (cmp102PhysicalBackgroundShiftCLM
                  U ha hP hε hsmall hbudget (A, D))) *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1 := by
    simpa only [cmp102PhysicalBackgroundShiftCLM_apply] using
      (BD.intrinsic_relative U X)
  exact
    isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation_of_ballData
      U ha hP hε hsmall hbudget A ρ r s B hρ hcontract D hD
      hlocal hrelative

/-- Smooth (`C∞`) certificate-generated implicit-function datum. -/
theorem
    isContDiffImplicitAt_top_cmp102IntrinsicPhysicalBackgroundCorrectionEquation_of_generatedBallData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (hρ : 0 < ρ) (hcontract : B.contractionRate < 1)
    (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ) :
    IsContDiffImplicitAt ⊤
      (cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget)
      (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc) -
        fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D))
      (A, D) := by
  let X :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
      (physicalGaugeOneCochainSupEquiv.symm D)
  let BD := B.chartBudget D hD
  have hlocal :
      ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x
          (cmp102PhysicalCochainToAmbientCLM
            (cmp102PhysicalBackgroundShiftCLM
              U ha hP hε hsmall hbudget (A, D)))‖ < 1 := by
    simpa only [cmp102PhysicalBackgroundShiftCLM_apply] using
      (BD.intrinsic_local U X)
  have hrelative :
      ∀ b : PhysicalBond d N',
        ‖cmp102AmbientNonlinearBlock U b
              (cmp102PhysicalCochainToAmbientCLM
                (cmp102PhysicalBackgroundShiftCLM
                  U ha hP hε hsmall hbudget (A, D))) *
            cmp98Eq119NonlinearBlockInverseAtZero U
              (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1 := by
    simpa only [cmp102PhysicalBackgroundShiftCLM_apply] using
      (BD.intrinsic_relative U X)
  apply
    isContDiffImplicitAt_top_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
      U ha hP hε hsmall hbudget A D hlocal hrelative
  exact
    (norm_cmp102IntrinsicPhysicalBackgroundCorrectionMap_verticalFDeriv_le
      U ha hP hε hsmall hbudget A ρ r s B hρ D hD hlocal hrelative
    ).trans_lt hcontract

/-- The local implicit solution furnished by the physical equation is `C²`
at the base fine field. -/
theorem
    contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionImplicitFunction
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp102PhysicalBackgroundShiftCLM
            U ha hP hε hsmall hbudget (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp102PhysicalBackgroundShiftCLM
                U ha hP hε hsmall hbudget (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1)
    (hvertical :
      ‖(fderiv ℝ
          (fun p :
              FinePhysicalOneCochain d L N' Nc ×
                PhysicalGaugeOneCochainSup d N' Nc =>
            cmp102IntrinsicPhysicalBackgroundCorrectionMap
              U ha hP hε hsmall hbudget p.1 p.2)
          (A, D)).comp
        (ContinuousLinearMap.inr ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc))‖ < 1) :
    let h :=
      isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
        U ha hP hε hsmall hbudget A D hlocal hrelative hvertical
    ContDiffAt ℝ 2 h.implicitFunction A := by
  dsimp only
  exact
    (isContDiffImplicitAt_cmp102IntrinsicPhysicalBackgroundCorrectionEquation
      U ha hP hε hsmall hbudget A D hlocal hrelative hvertical
    ).contDiffAt_implicitFunction

end

end YangMills.RG
