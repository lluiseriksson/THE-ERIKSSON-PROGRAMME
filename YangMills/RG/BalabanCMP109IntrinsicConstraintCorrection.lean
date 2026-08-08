/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109ConstraintCorrectionFixedPoint
import YangMills.RG.BalabanCMP109ConstraintCorrectedFluctuation
import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic

/-!
# The field-dependent CMP109 constraint correction

The formalized flat-pivot realization of the CMP109 correction satisfies

`D_tilde(A) = C(A - h D_tilde(A))`,

where `h` is the sparse right inverse of the flat block constraint.  The
Banach theorem in `BalabanCMP109ConstraintCorrectionFixedPoint` proves a
unique solution for every certified input field but does not name the
resulting field-dependent function.

This file makes that canonical choice and removes the chart certificate from
its fixed-point equation.  The intrinsic equation uses the literal sparse
insertion `cmp96ConstraintPivotInsertion`; it is not the CMP102 background
minimizer equation involving `H`.

Honest scope: joint smoothness of the fixed-point equation is proved, but no
regularity of the chosen solution function is asserted here.  The
implicit-function theorem, derivatives of `D_tilde`, the Jacobian term in
CMP109 (2.12), localization, and equation (1.36) remain separate obligations.
In addition, CMP109 describes its source `h(c)` through the inverse pivot
coefficient of the printed linear constraint `Q_tilde`; identifying that
operator with `cmp96ConstraintPivotInsertion` requires a separate corridor
gauge/dictionary theorem and is not asserted by this file.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The certificate-free flat-pivot fixed-point map
`D ↦ C_intrinsic(A - h D)` in the source sup norm. -/
noncomputable def cmp109IntrinsicConstraintCorrectionMap
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  physicalGaugeOneCochainSupEquiv
    (cmp102IntrinsicPhysicalNonlinearCorrection U
      (A - cmp96ConstraintPivotInsertion (L := L)
        (physicalGaugeOneCochainSupEquiv.symm D)))

/-- The joint linear shift `(A,D) ↦ A - hD` for the formalized flat-pivot
constraint-correction equation. -/
noncomputable def cmp109PhysicalConstraintShiftCLM :
    (FinePhysicalOneCochain d L N' Nc ×
      PhysicalGaugeOneCochainSup d N' Nc) →L[ℝ]
        FinePhysicalOneCochain d L N' Nc :=
  ContinuousLinearMap.fst ℝ
      (FinePhysicalOneCochain d L N' Nc)
      (PhysicalGaugeOneCochainSup d N' Nc) -
    (cmp96ConstraintPivotInsertionCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)).comp
      (physicalGaugeOneCochainSupEquiv.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ
          (FinePhysicalOneCochain d L N' Nc)
          (PhysicalGaugeOneCochainSup d N' Nc)))

@[simp] theorem cmp109PhysicalConstraintShiftCLM_apply
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    cmp109PhysicalConstraintShiftCLM (L := L) (A, D) =
      A - cmp96ConstraintPivotInsertion (L := L)
        (physicalGaugeOneCochainSupEquiv.symm D) := rfl

/-- The certificate-free CMP109 fixed-point equation is jointly `C∞` at every
point where the two literal Mercator deviations of its shifted field lie in
their open unit balls.  No regularity of chart certificates or of a selected
fixed point is assumed. -/
theorem contDiffAt_cmp109IntrinsicConstraintCorrectionMap_uncurry
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hlocal : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x
        (cmp102PhysicalCochainToAmbientCLM
          (cmp109PhysicalConstraintShiftCLM (L := L) (A, D)))‖ < 1)
    (hrelative : ∀ b : PhysicalBond d N',
      ‖cmp102AmbientNonlinearBlock U b
            (cmp102PhysicalCochainToAmbientCLM
              (cmp109PhysicalConstraintShiftCLM (L := L) (A, D))) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b - 1‖ < 1) :
    ContDiffAt ℝ ⊤
      (fun p :
          FinePhysicalOneCochain d L N' Nc ×
            PhysicalGaugeOneCochainSup d N' Nc =>
        cmp109IntrinsicConstraintCorrectionMap U p.1 p.2)
      (A, D) := by
  let shift :=
    cmp109PhysicalConstraintShiftCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)
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
        (A, D) :=
    ((physicalGaugeOneCochainSupEquiv :
        CoarsePhysicalOneCochain d N' Nc ≃L[ℝ]
          PhysicalGaugeOneCochainSup d N' Nc).toContinuousLinearMap
      ).contDiff.contDiffAt.comp (A, D) hcomp
  simpa [cmp109IntrinsicConstraintCorrectionMap, shift,
    cmp109PhysicalConstraintShiftCLM] using hout

/-- On a certified ball, the Banach map is literally the intrinsic CMP109
map.  The chart is used only to certify the open Mercator domain. -/
theorem cmp109ConstraintCorrectionMap_eq_intrinsic_of_mem
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP109ConstraintCorrectionBallData U A ρ r s)
    (D : PhysicalGaugeOneCochainSup d N' Nc)
    (hD : ‖D‖ ≤ ρ) :
    cmp109ConstraintCorrectionMap U A ρ r s B D =
      cmp109IntrinsicConstraintCorrectionMap U A D := by
  rw [B.correctionMap_eq_of_mem D hD]
  unfold cmp109IntrinsicConstraintCorrectionMap
  congr 1
  apply cmp102PhysicalNonlinearCorrectionOfBudget_eq_intrinsic
  intro b x hx
  exact ((B.chartBudget D hD).base b x hx).trans_lt (by norm_num)

/-- The unique CMP109 correction associated to every certified fine field. -/
noncomputable def cmp109PhysicalConstraintCorrection
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (ρ r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP109ConstraintCorrectionBallData
      U A (ρ A) (r A) (s A))
    (hcontract : ∀ A, (S A).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    CoarsePhysicalOneCochain d N' Nc :=
  physicalGaugeOneCochainSupEquiv.symm
    (Classical.choose
      ((S A).existsUnique_constraintCorrection (hcontract A)))

/-- The chosen source correction lies in its certified sup-norm ball. -/
theorem cmp109PhysicalConstraintCorrection_mem_ball
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (ρ r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP109ConstraintCorrectionBallData
      U A (ρ A) (r A) (s A))
    (hcontract : ∀ A, (S A).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp102PhysicalCorrectionSupNorm
        (cmp109PhysicalConstraintCorrection U ρ r s S hcontract A) ≤
      ρ A := by
  rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  simpa [cmp109PhysicalConstraintCorrection] using
    (Classical.choose_spec
      ((S A).existsUnique_constraintCorrection (hcontract A))).1.1

/-- The selected correction satisfies the certificate-free flat-pivot
fixed-point equation. -/
theorem cmp109PhysicalConstraintCorrection_intrinsicEquation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (ρ r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP109ConstraintCorrectionBallData
      U A (ρ A) (r A) (s A))
    (hcontract : ∀ A, (S A).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp109IntrinsicConstraintCorrectionMap U A
        (physicalGaugeOneCochainSupEquiv
          (cmp109PhysicalConstraintCorrection U ρ r s S hcontract A)) =
      physicalGaugeOneCochainSupEquiv
        (cmp109PhysicalConstraintCorrection U ρ r s S hcontract A) := by
  let D : PhysicalGaugeOneCochainSup d N' Nc :=
    Classical.choose
      ((S A).existsUnique_constraintCorrection (hcontract A))
  have hspec :=
    Classical.choose_spec
      ((S A).existsUnique_constraintCorrection (hcontract A))
  have hmap :=
    cmp109ConstraintCorrectionMap_eq_intrinsic_of_mem
      U A (ρ A) (r A) (s A) (S A) D hspec.1.1
  have hfix : cmp109IntrinsicConstraintCorrectionMap U A D = D := by
    rw [← hmap]
    exact hspec.1.2
  simpa [D, cmp109PhysicalConstraintCorrection] using hfix

/-- Uniqueness of the intrinsic CMP109 fixed point on a source-certified
ball.  This is the comparison principle needed to identify the canonical
choice above with a local implicit-function branch. -/
theorem cmp109IntrinsicConstraintCorrectionMap_fixedPoint_unique
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP109ConstraintCorrectionBallData U A ρ r s)
    (hcontract : B.contractionRate < 1)
    (D E : PhysicalGaugeOneCochainSup d N' Nc)
    (hD : ‖D‖ ≤ ρ) (hE : ‖E‖ ≤ ρ)
    (hfixD : cmp109IntrinsicConstraintCorrectionMap U A D = D)
    (hfixE : cmp109IntrinsicConstraintCorrectionMap U A E = E) :
    D = E := by
  rcases B.existsUnique_constraintCorrection hcontract with
    ⟨F, _, hunique⟩
  have hcertD :
      cmp109ConstraintCorrectionMap U A ρ r s B D = D := by
    rw [cmp109ConstraintCorrectionMap_eq_intrinsic_of_mem
      U A ρ r s B D hD]
    exact hfixD
  have hcertE :
      cmp109ConstraintCorrectionMap U A ρ r s B E = E := by
    rw [cmp109ConstraintCorrectionMap_eq_intrinsic_of_mem
      U A ρ r s B E hE]
    exact hfixE
  exact (hunique D ⟨hD, hcertD⟩).trans
    (hunique E ⟨hE, hcertE⟩).symm

/-- Intrinsic CMP109 fixed points produced by two source certificates at the
same fine field agree.  The proof uses only that both certified balls are
centred at zero: the point in the smaller ball also lies in the larger one,
where intrinsic uniqueness applies. -/
theorem cmp109IntrinsicConstraintCorrectionMap_fixedPoint_unique_across_certificates
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ₁ r₁ s₁ ρ₂ r₂ s₂ : ℝ)
    (B₁ : CMP109ConstraintCorrectionBallData U A ρ₁ r₁ s₁)
    (B₂ : CMP109ConstraintCorrectionBallData U A ρ₂ r₂ s₂)
    (hcontract₁ : B₁.contractionRate < 1)
    (hcontract₂ : B₂.contractionRate < 1)
    (D E : PhysicalGaugeOneCochainSup d N' Nc)
    (hD : ‖D‖ ≤ ρ₁) (hE : ‖E‖ ≤ ρ₂)
    (hfixD : cmp109IntrinsicConstraintCorrectionMap U A D = D)
    (hfixE : cmp109IntrinsicConstraintCorrectionMap U A E = E) :
    D = E := by
  rcases le_total ρ₁ ρ₂ with hρ | hρ
  · exact cmp109IntrinsicConstraintCorrectionMap_fixedPoint_unique
      U A ρ₂ r₂ s₂ B₂ hcontract₂ D E (hD.trans hρ) hE hfixD hfixE
  · exact cmp109IntrinsicConstraintCorrectionMap_fixedPoint_unique
      U A ρ₁ r₁ s₁ B₁ hcontract₁ D E hD (hE.trans hρ) hfixD hfixE

/-- The literal corrected fluctuation with the uniquely selected
field-dependent CMP109 correction. -/
noncomputable def cmp109PhysicalConstraintCorrectedFluctuation
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (ρ r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP109ConstraintCorrectionBallData
      U A (ρ A) (r A) (s A))
    (hcontract : ∀ A, (S A).contractionRate < 1)
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc) :
    FinePhysicalOneCochain d L N' Nc :=
  let A := cmp109ConstrainedLinearFluctuation (L := L) gk B
  cmp109ConstraintCorrectedFluctuation (L := L) gk B
    (cmp109PhysicalConstraintCorrection U ρ r s S hcontract A)

/-- Evaluation exposes exactly the printed corrected-field formula. -/
theorem cmp109PhysicalConstraintCorrectedFluctuation_eq
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (ρ r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP109ConstraintCorrectionBallData
      U A (ρ A) (r A) (s A))
    (hcontract : ∀ A, (S A).contractionRate < 1)
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc) :
    cmp109PhysicalConstraintCorrectedFluctuation
        U ρ r s S hcontract gk B =
      cmp109ConstrainedLinearFluctuation (L := L) gk B -
        cmp96ConstraintPivotInsertion (L := L)
          (cmp109PhysicalConstraintCorrection U ρ r s S hcontract
            (cmp109ConstrainedLinearFluctuation (L := L) gk B)) := rfl

end

end YangMills.RG
