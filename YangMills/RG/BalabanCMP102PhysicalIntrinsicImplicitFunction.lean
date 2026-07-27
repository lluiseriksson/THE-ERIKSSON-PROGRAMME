/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPointSmooth
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

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

The vertical derivative bound remains deliberately visible here.  It must be
derived from the physical two-field CMP102 estimates before this result is
used to remove the legacy `hD` premise from the radial decomposition.
-/

open Function

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
