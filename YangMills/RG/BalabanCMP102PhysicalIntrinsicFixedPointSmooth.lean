/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicFixedPoint

/-!
# Joint smoothness of the intrinsic CMP102 fixed-point map

The implicit equation depends on the pair `(A,D)` only through the linear
physical shift `A - H D`.  Composing that shift with the intrinsic analytic
equation-(122) correction gives joint smoothness without any regularity
assumption on a selected fixed point or on scalar chart certificates.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The joint linear source map `(A,D) ↦ A - H D`. -/
noncomputable def cmp102PhysicalBackgroundShiftCLM
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    (FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc) →L[ℝ]
        FinePhysicalOneCochain d L N' Nc :=
  ContinuousLinearMap.fst ℝ
      (FinePhysicalOneCochain d L N' Nc)
      (PhysicalGaugeOneCochainSup d N' Nc) -
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget).comp
      (physicalGaugeOneCochainSupEquiv.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc)))

@[simp] theorem cmp102PhysicalBackgroundShiftCLM_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    cmp102PhysicalBackgroundShiftCLM
        U ha hP hε hsmall hbudget (A, D) =
      A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D) := rfl

/-- **Source-specific joint smoothness producer.**  The certificate-free
fixed-point map is `C∞` at `(A,D)` whenever the literal inner and final
Mercator deviations at the shifted physical field lie in their open unit
balls. -/
theorem contDiffAt_cmp102IntrinsicPhysicalBackgroundCorrectionMap_uncurry
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
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1) :
    ContDiffAt ℝ ⊤
      (fun p :
          FinePhysicalOneCochain d L N' Nc ×
            PhysicalGaugeOneCochainSup d N' Nc =>
        cmp102IntrinsicPhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget p.1 p.2)
      (A, D) := by
  let shift :=
    cmp102PhysicalBackgroundShiftCLM
      U ha hP hε hsmall hbudget
  have hC :
      ContDiffAt ℝ ⊤
        (cmp102IntrinsicPhysicalNonlinearCorrection U)
        (shift (A, D)) :=
    contDiffAt_cmp102IntrinsicPhysicalNonlinearCorrection
      U (shift (A, D)) hlocal hrelative
  have hcomp :
      ContDiffAt ℝ ⊤
        (fun p :
            FinePhysicalOneCochain d L N' Nc ×
              PhysicalGaugeOneCochainSup d N' Nc =>
          cmp102IntrinsicPhysicalNonlinearCorrection U (shift p))
        (A, D) := by
    simpa only [Function.comp_apply] using
      hC.comp (A, D) shift.contDiff.contDiffAt
  have hout :
      ContDiffAt ℝ ⊤
        (fun p :
            FinePhysicalOneCochain d L N' Nc ×
              PhysicalGaugeOneCochainSup d N' Nc =>
          physicalGaugeOneCochainSupEquiv
            (cmp102IntrinsicPhysicalNonlinearCorrection U (shift p)))
        (A, D) := by
    exact
      physicalGaugeOneCochainSupEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp
        (A, D) hcomp
  simpa [cmp102IntrinsicPhysicalBackgroundCorrectionMap, shift,
    cmp102PhysicalBackgroundShiftCLM] using hout

end

end YangMills.RG
