/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrectionFirstOrder
import YangMills.RG.BalabanCMP116RadialTaylorOperator

/-!
# Radial equation-(1.42) operator for the corrected CMP102 potential

The physically corrected equation-(80) potential is now inserted directly
into the radial Taylor construction.  Its value and first derivative at zero
are produced internally.  Only the genuine `C²` regularity needed to define
the radial Hessian average remains an analytic input.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The radial Hessian operator attached to the physical equation-(80)
potential with fixed source chart radii. -/
noncomputable def cmp102Eq80CorrectedPhysicalRadialOperator
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
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hsmooth : ContDiff ℝ 2
      (cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J))
    (A : FinePhysicalOneCochain d L N' Nc) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  cmp116RadialTaylorOperator
    (cmp102Eq80CorrectedPhysicalGlobalPotential
      U ha hP hε hsmall hbudget ρ radius
      (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J)
    A hsmooth

set_option maxHeartbeats 10000000 in
/-- **Literal radial decomposition of the physical equation-(80)
potential.**  No value, derivative, or differentiability premise for the
implicit correction appears in the interface. -/
theorem cmp102Eq80CorrectedPhysicalGlobalPotential_eq_radial_constRadii
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
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (D₃ : FinePhysicalOneCochain d L N' Nc →
      CoarsePhysicalOneCochain d N' Nc)
    (V₀ : FinePhysicalOneCochain d L N' Nc → ℝ)
    (Δπ : FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc)
    (J : FinePhysicalOneCochain d L N' Nc)
    (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0)
    (hD₃ : HasFDerivAt D₃
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ]
        CoarsePhysicalOneCochain d N' Nc) 0)
    (hV₀ : HasFDerivAt V₀
      (0 : FinePhysicalOneCochain d L N' Nc →L[ℝ] ℝ) 0)
    (hsmooth : ContDiff ℝ 2
      (cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J))
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp102Eq80CorrectedPhysicalGlobalPotential
        U ha hP hε hsmall hbudget ρ radius
        (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J A =
      (1 / 2 : ℝ) * inner ℝ A
        (cmp102Eq80CorrectedPhysicalRadialOperator
          U ha hP hε hsmall hbudget ρ radius r s S hcontract
          D₃ V₀ Δπ J hsmooth A A) := by
  let f :=
    cmp102Eq80CorrectedPhysicalGlobalPotential
      U ha hP hε hsmall hbudget ρ radius
      (fun _ => r) (fun _ => s) S hcontract D₃ V₀ Δπ J
  have hf0 : f 0 = 0 := by
    exact cmp102Eq80CorrectedPhysicalGlobalPotential_zero
      U ha hP hε hsmall hbudget ρ radius
      (fun _ => r) (fun _ => s) S hcontract
      D₃ V₀ Δπ J hD₃0 hV₀0
  have hdf0 : fderiv ℝ f 0 = 0 :=
    (cmp102Eq80CorrectedPhysicalGlobalPotential_hasFDerivAt_zero_constRadii
      U ha hP hε hsmall hbudget ρ radius r s S hcontract
      D₃ V₀ Δπ J hD₃0 hD₃ hV₀).fderiv
  simpa [f, cmp102Eq80CorrectedPhysicalRadialOperator] using
    cmp116RadialTaylorOperator_eq_of_normalized f A hsmooth hf0 hdf0

end

end YangMills.RG
