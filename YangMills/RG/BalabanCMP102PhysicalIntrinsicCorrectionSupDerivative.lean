/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionSourceDerivative
import YangMills.RG.BalabanCMP102PhysicalSupNormTransport

/-!
# Uniform source derivative budget for the intrinsic physical correction

The physical correction is stored in finite `L²` coordinates, whereas the
CMP102 contraction argument uses the volume-uniform bond supremum.  This
module transports the literal intrinsic correction to `PiLp ∞`, identifies
its derivative coordinatewise, and takes the supremum of the already
source-generated one-bond bounds.  No dimension factor or caller-supplied
derivative estimate is introduced.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
  [NeZero (M * N')]

/-- The intrinsic physical correction equipped with the source-facing
bond-supremum norm. -/
noncomputable def cmp102IntrinsicPhysicalNonlinearCorrectionSup
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  physicalGaugeOneCochainSupEquiv
    (cmp102IntrinsicPhysicalNonlinearCorrection U A)

@[simp] theorem cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp102IntrinsicPhysicalNonlinearCorrectionSup U A b =
      cmp102IntrinsicPhysicalCorrectionBondCoord U b A := by
  rfl

/-- The derivative of the sup-norm correction is the family of the literal
one-bond derivatives. -/
theorem fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A H : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hlocal : ∀ c : PhysicalBond d N', ∀ x ∈ blockOf M N' c.1,
      ‖cmp98UbarAmbientDeviationMatrix U c x
        (cmp102PhysicalCochainToAmbientCLM A)‖ < 1)
    (hrelative : ∀ c : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U c
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) c - 1‖ < 1) :
    fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) A H b =
      fderiv ℝ (cmp102IntrinsicPhysicalCorrectionBondCoord U b) A H := by
  have hdiff :
      DifferentiableAt ℝ
        (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) A := by
    unfold cmp102IntrinsicPhysicalNonlinearCorrectionSup
    have hin :
        DifferentiableAt ℝ
          (cmp102IntrinsicPhysicalNonlinearCorrection U) A :=
      (contDiffAt_cmp102IntrinsicPhysicalNonlinearCorrection
        U A hlocal hrelative).differentiableAt (by simp)
    exact
      physicalGaugeOneCochainSupEquiv.toContinuousLinearMap.differentiableAt.comp
        A hin
  have hproj :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) ⊤
      (cmp102IntrinsicPhysicalNonlinearCorrectionSup U A) b).comp
        A hdiff.hasFDerivAt
  have happ := congrArg (fun L => L H) hproj.fderiv
  simpa only [cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply] using happ.symm

/-- **Volume-uniform source producer.**  Uniform physical source conditions
on every coarse bond imply the same derivative-Lipschitz budget in the
`PiLp ∞` norm.  Taking the bond supremum costs no cardinality factor. -/
theorem norm_fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_sub_apply_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B H : PhysicalGaugeOneCochain d (M * N') Nc)
    {r q s : ℝ}
    (hr : 0 ≤ r) (hq13 : 1 / 3 ≤ q) (hq1 : q < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hA : ‖cmp102PhysicalCochainToAmbientCLM A‖ ≤ r)
    (hB : ‖cmp102PhysicalCochainToAmbientCLM B‖ ≤ r)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDA : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM A)‖ ≤ q)
    (hDB : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM B)‖ ≤ q)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r q ≤ s) :
    ‖(fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) A -
        fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) B) H‖ ≤
      cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
          d M N' Nc r q s *
        ‖A - B‖ * ‖H‖ := by
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  have hrelativeA : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1 := by
    intro b
    exact ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b (cmp102PhysicalCochainToAmbientCLM A)
      hr hq13 hq1 hA (hbase b) (hDA b)).trans hdev).trans_lt hs1
  have hrelativeB : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM B) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ < 1 := by
    intro b
    exact ((norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b (cmp102PhysicalCochainToAmbientCLM B)
      hr hq13 hq1 hB (hbase b) (hDB b)).trans hdev).trans_lt hs1
  rw [PiLp.norm_eq_ciSup]
  apply ciSup_le
  intro b
  change
    ‖fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) A H b -
        fderiv ℝ (cmp102IntrinsicPhysicalNonlinearCorrectionSup U) B H b‖ ≤
      cmp102SourceIntrinsicPhysicalCorrectionBondDerivativeLipschitzBudget
          d M N' Nc r q s * ‖A - B‖ * ‖H‖
  rw [
    fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply
      U A H b (fun c x hx => (hDA c x hx).trans_lt hq1) hrelativeA,
    fderiv_cmp102IntrinsicPhysicalNonlinearCorrectionSup_apply
      U B H b (fun c x hx => (hDB c x hx).trans_lt hq1) hrelativeB]
  exact
    norm_fderiv_cmp102IntrinsicPhysicalCorrectionBondCoord_sub_apply_le_sourceBudget
      U b A B H hr hq13 hq1 hs0 hs1 hA hB
      (hbase b) (hDA b) (hDB b) hdev

end

end YangMills.RG
