/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalGreenFiniteGridAliasing
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn
import YangMills.RG.BalabanCMP99SourceFlowFlatPrecisionScalarDictionary

/-!
# Source-flow endpoint at the zero alias residue

The point-source endpoint produced in C1b is indexed by periodic Fourier
negation.  This module performs the two exact finite reindexings and then
specializes physical finite-grid aliasing to the zero residue class with the
literal source-flow coefficient `cmp99SourceFlowFlatFullComplexA a L depth`.
Its positivity is constructed internally from `ha : 0 < a`.

No generated coefficient, Fourier reconstruction, inverse, Green family,
coefficient bound, owner estimate, regional `B0`, window-15 attainment or
terminal field is assumed or asserted.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

private theorem sourceFlow_fourierNeg_involutive
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FinBoxFourierNeg (cmp99FinBoxFourierNeg k) = k := by
  apply (cmp99FinBoxZModEquiv d N).injective
  simp only [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]

private def sourceFlowFourierNegSelfEquiv
    (d N : ℕ) [NeZero N] : FinBox d N ≃ FinBox d N where
  toFun := cmp99FinBoxFourierNeg
  invFun := cmp99FinBoxFourierNeg
  left_inv := sourceFlow_fourierNeg_involutive
  right_inv := sourceFlow_fourierNeg_involutive

private theorem sourceFlow_sum_comp_fourierNeg
    {d N : ℕ} [NeZero N]
    {A : Type*} [AddCommMonoid A] (f : FinBox d N → A) :
    (∑ ell : FinBox d N, f (cmp99FinBoxFourierNeg ell)) =
      ∑ ell : FinBox d N, f ell := by
  exact Equiv.sum_comp (sourceFlowFourierNegSelfEquiv d N) f

/-- The normalized finite endpoint sum with the literal source-flow
coefficient is exactly the zero-residue physical Green series. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatPhysical_normalized_sum_endpointIntegrand_eq_zeroResidue
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {a rho : ℝ} (ha : 0 < a)
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceFlowFlatFullComplexA a L depth) rho)
    (u : Fin 4 → ℤ) :
    ((((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹) *
        ∑ ell : FinBox 4 (2 * (K * Q)),
          cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
            4 (L ^ (depth + 1)) 1 0
            (cmp99SourceFlowFlatFullComplexA a L depth)
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
              (cmp99FinBoxFourierNeg ell))
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ (depth + 1) : ℕ) : ℝ)⁻¹) u) =
      ∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          u n := by
  let N : ℕ := 2 * (K * Q)
  let Kfine : ℕ := L ^ (depth + 1)
  let weightedA : ℝ := cmp99SourceFlowFlatFullComplexA a L depth
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  have hA : 0 < weightedA := by
    dsimp [weightedA, cmp99SourceFlowFlatFullComplexA]
    exact cmp99SourceMassParameter_pos ha
      (by exact_mod_cast (NeZero.pos L)) depth
  let endpoint : FinBox 4 N → ℂ := fun ell =>
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
      4 Kfine 1 0 weightedA
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        ((Kfine : ℝ)⁻¹) u)
  have hneg :
      (∑ ell : FinBox 4 N,
          endpoint (cmp99FinBoxFourierNeg ell)) =
        ∑ ell : FinBox 4 N, endpoint ell :=
    sourceFlow_sum_comp_fourierNeg endpoint
  have hbox :
      (∑ ell : FinBox 4 N, endpoint ell) =
        ∑ k : CMP99FlatZModBox 4 N,
          endpoint ((cmp99FinBoxZModEquiv 4 N).symm k) := by
    simpa using
      (Equiv.sum_comp (cmp99FinBoxZModEquiv 4 N)
        (fun k : CMP99FlatZModBox 4 N =>
          endpoint ((cmp99FinBoxZModEquiv 4 N).symm k)))
  have halias :=
    cmp99Flat_normalizedFiniteGridPhysicalGreenSample_eq_residueClass_draft
      (K := Kfine) (N := N) (a := weightedA) (rho := rho)
      hA hrho hamplitude hradius hwindow u (0 : CMP99FlatZModBox 4 N)
  change (((N : ℂ) ^ 4)⁻¹) *
      ∑ ell : FinBox 4 N,
        endpoint (cmp99FinBoxFourierNeg ell) = _
  rw [hneg, hbox]
  simpa [cmp99FlatZModFourierCharacter, endpoint, Kfine, N, weightedA]
    using halias

end

end YangMills.RG
