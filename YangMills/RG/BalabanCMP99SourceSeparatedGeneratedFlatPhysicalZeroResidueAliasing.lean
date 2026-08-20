/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalGreenFiniteGridAliasing
import YangMills.RG.BalabanCMP99SourceFlatWeightedAdjointScalarColumn

/-!
# Source-separated generated endpoint at the zero alias residue

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

The point-source endpoint produced in C1b is indexed by the periodic negative
of a literal `FinBox` momentum.  Step 8b.22/Unit E is indexed instead by the
corresponding uncentered `ZMod` sample.  This module performs exactly those
two finite reindexings and then specializes physical finite-grid aliasing to
the zero residue class.

The stabilizing coefficient is the internally generated physical coefficient.
Only the common analytic radius and its two literal source windows remain as
inputs.  No Fourier reconstruction, inverse, Green family, coefficient bound,
regional `B0`, window-15 attainment or terminal field is assumed or asserted.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The periodic Fourier-negation map used by this aliasing bridge is an
involution.  The proof is transported through the literal `FinBox`/`ZMod`
equivalence, so no centered-representative equality is assumed. -/
theorem cmp99FinBoxFourierNeg_involutive_for_zeroResidueAliasing
    {d N : ℕ} [NeZero N] (k : FinBox d N) :
    cmp99FinBoxFourierNeg (cmp99FinBoxFourierNeg k) = k := by
  apply (cmp99FinBoxZModEquiv d N).injective
  simp only [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]

/-- Periodic Fourier negation as a self-equivalence of the literal finite
momentum box.  Its inverse is constructed from the proved involution; no
identification of representatives is assumed. -/
def cmp99FinBoxFourierNegSelfEquiv
    (d N : ℕ) [NeZero N] : FinBox d N ≃ FinBox d N where
  toFun := cmp99FinBoxFourierNeg
  invFun := cmp99FinBoxFourierNeg
  left_inv := cmp99FinBoxFourierNeg_involutive_for_zeroResidueAliasing
  right_inv := cmp99FinBoxFourierNeg_involutive_for_zeroResidueAliasing

/-- A finite sum is unchanged when every momentum is reindexed by periodic
Fourier negation. -/
theorem sum_comp_cmp99FinBoxFourierNeg
    {d N : ℕ} [NeZero N]
    {A : Type*} [AddCommMonoid A] (f : FinBox d N → A) :
    (∑ ell : FinBox d N, f (cmp99FinBoxFourierNeg ell)) =
      ∑ ell : FinBox d N, f ell := by
  exact Equiv.sum_comp (cmp99FinBoxFourierNegSelfEquiv d N) f

/-- The normalized sum used by the source-separated generated point-source
endpoint is exactly the zero-residue physical Green series.  The generated
coefficient and the fine/coarse scale dictionary occur literally in the
conclusion; only the source analytic window remains visible. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysical_normalized_sum_endpointIntegrand_eq_zeroResidue
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {rho : ℝ}
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) rho)
    (u : Fin 4 → ℤ) :
    ((((2 * (K * Q) : ℕ) : ℂ) ^ 4)⁻¹) *
        ∑ ell : FinBox 4 (2 * (K * Q)),
          cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
            4 (L ^ (depth + 1)) 1 0
            (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
              (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
              (cmp99FinBoxFourierNeg ell))
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L ^ (depth + 1) : ℕ) : ℝ)⁻¹) u) =
      ∑' n : CMP99FlatIntegerResidueClass 4 (2 * (K * Q)) 0,
        cmp89Eq248CenteredGreenPhysicalFourierCoefficient
          (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          u n := by
  let N : ℕ := 2 * (K * Q)
  let Kfine : ℕ := L ^ (depth + 1)
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  let endpoint : FinBox 4 N → ℂ := fun ell =>
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand
      4 Kfine 1 0 a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        ((Kfine : ℝ)⁻¹) u)
  have hneg :
      (∑ ell : FinBox 4 N,
          endpoint (cmp99FinBoxFourierNeg ell)) =
        ∑ ell : FinBox 4 N, endpoint ell :=
    sum_comp_cmp99FinBoxFourierNeg endpoint
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
      (K := Kfine) (N := N) (a := a) (rho := rho)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth)
      hrho hamplitude hradius hwindow u (0 : CMP99FlatZModBox 4 N)
  change (((N : ℂ) ^ 4)⁻¹) *
      ∑ ell : FinBox 4 N,
        endpoint (cmp99FinBoxFourierNeg ell) = _
  rw [hneg, hbox]
  simpa [cmp99FlatZModFourierCharacter, endpoint, Kfine, N, a] using halias

end

end YangMills.RG
