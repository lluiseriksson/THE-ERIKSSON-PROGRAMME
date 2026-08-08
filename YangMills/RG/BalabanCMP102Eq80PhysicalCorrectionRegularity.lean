/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionLipschitz
import YangMills.RG.BalabanCMP102PhysicalIntrinsicImplicitFunction

/-!
# Source-specific regularity of the selected CMP102 correction

The selected correction is continuous by its physical two-field estimate.
At every fine field its graph satisfies the certificate-free intrinsic
equation.  The physically generated implicit-function package therefore
identifies that graph locally with the `C²` implicit solution.

No regularity of the scalar certificate family is assumed.
-/

namespace YangMills.RG

open YangMills Function Filter
open scoped Topology

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

set_option maxHeartbeats 10000000 in
/-- The sup-norm realization of the selected physical correction is `C²`
at every fine field.  Positivity of the Banach radius is the only additional
nondegeneracy condition beyond the physical scalar certificate. -/
theorem contDiffAt_top_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ContDiffAt ℝ ⊤
      (fun X =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract X))
      A := by
  let Dfun :=
    fun X : FinePhysicalOneCochain d L N' Nc =>
      physicalGaugeOneCochainSupEquiv
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius
            (fun _ => r) (fun _ => s) S hcontract X)
  let F :=
    cmp102IntrinsicPhysicalBackgroundCorrectionEquation
      U ha hP hε hsmall hbudget
  have hDmem : ‖Dfun A‖ ≤ ρ A := by
    simpa [Dfun, norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
      using cmp102Eq80PhysicalBackgroundCorrection_mem_ball
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract A
  let himp :=
    isContDiffImplicitAt_top_cmp102IntrinsicPhysicalBackgroundCorrectionEquation_of_generatedBallData
      U ha hP hε hsmall hbudget A (ρ A) r s (S A).toBallData
        (hρ A) (hcontract A) (Dfun A) hDmem
  have hDcontinuous : Continuous Dfun := by
    simpa [Dfun] using
      continuous_cmp102Eq80PhysicalBackgroundCorrection_sup
        U ha hP hε hsmall hbudget ρ radius r s S hcontract
  have hgraph :
      Tendsto (fun X => (X, Dfun X)) (𝓝 A) (𝓝 (A, Dfun A)) :=
    (continuousAt_id.prodMk hDcontinuous.continuousAt)
  have hzero :
      ∀ X, F (X, Dfun X) = 0 := by
    intro X
    have hfix :=
      cmp102Eq80PhysicalBackgroundCorrection_intrinsicEquation
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract X
    simp only [F, cmp102IntrinsicPhysicalBackgroundCorrectionEquation,
      Dfun, hfix, sub_self]
  have hevent :
      Dfun =ᶠ[𝓝 A] himp.implicitFunction := by
    have hpulled :=
      hgraph.eventually himp.eventually_implicitFunction_apply_eq
    filter_upwards [hpulled] with X hX
    have hzeroX :
        cmp102IntrinsicPhysicalBackgroundCorrectionEquation
            U ha hP hε hsmall hbudget (X, Dfun X) = 0 := by
      simpa [F] using hzero X
    have hzeroA :
        cmp102IntrinsicPhysicalBackgroundCorrectionEquation
            U ha hP hε hsmall hbudget (A, Dfun A) = 0 := by
      simpa [F] using hzero A
    exact (hX (hzeroX.trans hzeroA.symm)).symm
  exact
    (himp.contDiffAt_implicitFunction.congr_of_eventuallyEq hevent : _)

/-- Global `C²` regularity of the source-defined physical correction. -/
theorem contDiff_top_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    ContDiff ℝ ⊤
      (fun X =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract X)) :=
  contDiff_iff_contDiffAt.mpr fun A =>
    contDiffAt_top_cmp102Eq80PhysicalBackgroundCorrection_sup
      U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract A

/-- The selected correction is `C∞` in the original physical cochain
topology as well. -/
theorem contDiff_top_cmp102Eq80PhysicalBackgroundCorrection
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    ContDiff ℝ ⊤
      (cmp102Eq80PhysicalBackgroundCorrection
        U ha hP hε hsmall hbudget ρ radius
          (fun _ => r) (fun _ => s) S hcontract) := by
  have hsup :=
    contDiff_top_cmp102Eq80PhysicalBackgroundCorrection_sup
      U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract
  exact
    (physicalGaugeOneCochainSupEquiv.symm :
      PhysicalGaugeOneCochainSup d N' Nc ≃L[ℝ]
        CoarsePhysicalOneCochain d N' Nc).contDiff.comp hsup

/-- `C²` specialization of the smooth physical correction. -/
theorem contDiffAt_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    ContDiffAt ℝ 2
      (fun X =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract X))
      A :=
  (contDiffAt_top_cmp102Eq80PhysicalBackgroundCorrection_sup
    U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract A).of_le le_top

/-- Global `C²` specialization of the smooth physical correction. -/
theorem contDiff_cmp102Eq80PhysicalBackgroundCorrection_sup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius : FinePhysicalOneCochain d L N' Nc → ℝ)
    (r s : ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) r s)
    (hρ : ∀ A, 0 < ρ A)
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1) :
    ContDiff ℝ 2
      (fun X =>
        physicalGaugeOneCochainSupEquiv
          (cmp102Eq80PhysicalBackgroundCorrection
            U ha hP hε hsmall hbudget ρ radius
              (fun _ => r) (fun _ => s) S hcontract X)) :=
  (contDiff_top_cmp102Eq80PhysicalBackgroundCorrection_sup
    U ha hP hε hsmall hbudget ρ radius r s S hρ hcontract).of_le le_top

end

end YangMills.RG
