/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeZeroFibreEndpointReflection

/-!
# Complete physical-fibre endpoint integrand

PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the Lean compiler.

The column-oriented physical fibre is first reindexed through the literal
signed-alias equivalence and identified with the CMP89 stabilized endpoint
integrand.  The complete transpose sum is then treated by cases on the coarse
mode: nonzero fibres use the sealed Fourier-negation carry, while the zero
fibre uses the separately sealed Eq. (249) reflection without cancelling the
central mass-zero symbol.

The final statement has one literal endpoint-integrand target and no
piecewise wrapper.  It does not identify a Brillouin integral, construct
regional `B0`, attain window 15, discharge a terminal field or inhabit
`TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The complete column-oriented physical fibre is exactly the literal CMP89
stabilized endpoint integrand at its coarse base momentum. -/
theorem sum_cmp99SourceFlatPhysicalColumnGreenEndpointSample_eq_endpointIntegrand
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (mass a : ℝ)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalColumnGreenEndpointSample
          ell mass a x y k) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu)) := by
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
    d M N' ell
  let u := cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y
  let column := fun m : CMP89Eq246AliasIndex d M 1 =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) m.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu))) *
      cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) m
  calc
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalColumnGreenEndpointSample
          ell mass a x y k) =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        column (e k) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold cmp99SourceFlatPhysicalColumnGreenEndpointSample
      simp only [column, u, e]
    _ = ∑ m : CMP89Eq246AliasIndex d M 1, column m := by
      exact Equiv.sum_comp e column
    _ = cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu)) := by
      exact
        sum_exp_mul_cmp89Eq249StabilizedAliasColumnSolution_eq_endpointIntegrand
          d M 1 mass a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu => -u mu))

/-- The complete mass-zero transpose fibre sum is one literal CMP89 endpoint
integrand on every coarse mode.  The proof uses quotient transport only on
nonzero fibres and the sealed reflection only on the singular zero fibre. -/
theorem sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_eq_endpointIntegrand
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    (ell : FinBox d N')
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          ell 0 a x y k) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand d M 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
          (cmp99FinBoxFourierNeg ell))
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu)) := by
  by_cases hell : ell = 0
  · subst ell
    have hzero : cmp99FinBoxFourierNeg (0 : FinBox d N') = 0 := by
      apply (cmp99FinBoxZModEquiv d N').injective
      rw [cmp99FinBoxZModEquiv_fourierNeg]
      funext mu
      simp [cmp99FinBoxZModEquiv]
    simpa only [hzero,
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_zero] using
        (sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_zero_eq_endpointIntegrand
          (d := d) (M := M) (N' := N') (0 : ℝ) a x y)
  · calc
      (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
          cmp99SourceFlatPhysicalTransposeGreenEndpointSample
            ell 0 a x y k) =
        ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
            (cmp99FinBoxFourierNeg ell),
          cmp99SourceFlatPhysicalColumnGreenEndpointSample
            (cmp99FinBoxFourierNeg ell) 0 a x y k := by
        exact
          sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_fourierNeg_eq_column
            ha hell x y
      _ = _ := by
        exact
          sum_cmp99SourceFlatPhysicalColumnGreenEndpointSample_eq_endpointIntegrand
            (cmp99FinBoxFourierNeg ell) 0 a x y

end

end YangMills.RG
