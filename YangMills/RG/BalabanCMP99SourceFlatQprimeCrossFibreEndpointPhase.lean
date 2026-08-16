/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotient
import YangMills.RG.BalabanCMP99SourceFlatQprimeTransposeEndpointSample

/-!
# Cross-fibre endpoint phase under physical Fourier negation

PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the Lean compiler.

Periodic Fourier negation moves the physical fibre over `ell` to the fibre
over `cmp99FinBoxFourierNeg ell`.  This module transports the literal endpoint
phase through that equivalence and combines it with the sealed nonzero-fibre
row-to-column quotient identity.  The complete finite physical fibre sum is
reindexed; no distinguished alias is claimed to be preserved termwise.

The zero coarse fibre remains separate because its mass-zero central fine
symbol vanishes and quotient cancellation is unavailable there.  This file
does not identify that branch, construct a Brillouin integral or regional
`B0`, attain window 15, discharge a terminal field or inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The endpoint phase on the Fourier-negative physical fibre is the input
phase at the opposite fine-lattice displacement.  The full `2*pi*M` period
is discharged before the sign is moved from momentum to displacement. -/
theorem cmp99SourceFlatQprimeAliasEndpointPhase_fourierNeg_eq_negDisplacement
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
            (cmp99FinBoxFourierNeg ell)
            (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
              d M N' ell k)).1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k).1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
          (fun mu => -u mu))) := by
  let kneg :=
    cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv d M N' ell k
  rw [← cmp99SourceFlatQprimeAmplitudeMomentum_endpointPhase_eq_entireAlias
      (cmp99FinBoxFourierNeg ell) kneg u,
    ← cmp99SourceFlatQprimeAmplitudeMomentum_endpointPhase_eq_entireAlias
      ell k (fun mu => -u mu)]
  change Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp99SourceFlatQprimeAmplitudeMomentum
        (cmp99FinBoxFourierNeg k.1))
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) =
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp99SourceFlatQprimeAmplitudeMomentum k.1)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
        (fun mu => -u mu)))
  rcases
      cmp99SourceFlatQprimeAmplitudeMomentum_fourierNeg_eq_neg_add_period
        k.1 with
    ⟨w, hw⟩
  rw [hw]
  calc
    _ = Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (-cmp99SourceFlatQprimeAmplitudeMomentum k.1)
        (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹) u)) := by
      simpa only [Pi.neg_apply] using
        (exp_I_cmp89Eq251EntirePhase_add_int_aliasPeriods_physicalFine
          (N := M) (-cmp99SourceFlatQprimeAmplitudeMomentum k.1) w u)
    _ = _ := by
      congr 2
      simp only [cmp89Eq251EntirePhase,
        cmp89Eq249PhysicalFineLatticeDisplacement, Pi.neg_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro mu _
      ring

/-- One column-oriented endpoint sample on the Fourier-negative fibre.  Its
displacement is the literal opposite of the row-oriented physical sample. -/
def cmp99SourceFlatPhysicalColumnGreenEndpointSample
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (mass a : ℝ)
    (x : FinBox d (M * N')) (y : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) : ℂ :=
  Complex.exp (Complex.I * cmp89Eq251EntirePhase
      (cmp89Eq248EntireAliasMomentum
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
          d M N' ell k).1)
      (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
        (fun mu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu))) *
    cmp89Eq249StabilizedAliasColumnSolution d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell k)

/-- On a nonzero coarse fibre, one literal row-oriented endpoint sample is
the column-oriented sample of its actual Fourier-negative physical mode. -/
theorem cmp99SourceFlatPhysicalTransposeGreenEndpointSample_fourierNeg_eq_column
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox d N'} (hell : ell ≠ 0)
    (x : FinBox d (M * N')) (y : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatPhysicalTransposeGreenEndpointSample
        ell 0 a x y k =
      cmp99SourceFlatPhysicalColumnGreenEndpointSample
        (cmp99FinBoxFourierNeg ell) 0 a x y
        (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
          d M N' ell k) := by
  unfold cmp99SourceFlatPhysicalTransposeGreenEndpointSample
    cmp99SourceFlatPhysicalColumnGreenEndpointSample
  have hphase :=
    cmp99SourceFlatQprimeAliasEndpointPhase_fourierNeg_eq_negDisplacement
      ell k (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu)
  have hphase' :
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
              d M N' ell k).1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y))) =
        Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
              (cmp99FinBoxFourierNeg ell))
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
              (cmp99FinBoxFourierNeg ell)
              (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
                d M N' ell k)).1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                M x y mu))) := by
    simpa only [neg_neg] using hphase.symm
  have hsolution :
      cmp89Eq249StabilizedAliasTransposeSolution d M 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) =
        cmp89Eq249StabilizedAliasColumnSolution d M 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
            (cmp99FinBoxFourierNeg ell))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N'
            (cmp99FinBoxFourierNeg ell)
            (cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv
              d M N' ell k)) := by
    simpa only [cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution]
      using
        (cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution_coarseFourierNeg_eq_column
          ha hell k)
  rw [hphase', hsolution]

/-- The complete nonzero physical fibre sum is transported to the complete
column-oriented sum on the Fourier-negative fibre.  This is a reindexing of
the whole finite fibre, not a pointwise claim about a distinguished alias. -/
theorem sum_cmp99SourceFlatPhysicalTransposeGreenEndpointSample_fourierNeg_eq_column
    {d M N' : ℕ} [NeZero M] [NeZero N'] {a : ℝ} (ha : 0 < a)
    {ell : FinBox d N'} (hell : ell ≠ 0)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          ell 0 a x y k) =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
          (cmp99FinBoxFourierNeg ell),
        cmp99SourceFlatPhysicalColumnGreenEndpointSample
          (cmp99FinBoxFourierNeg ell) 0 a x y k := by
  let e :=
    cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv d M N' ell
  calc
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          ell 0 a x y k) =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalColumnGreenEndpointSample
          (cmp99FinBoxFourierNeg ell) 0 a x y (e k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample_fourierNeg_eq_column
          ha hell x y k
    _ = ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
          (cmp99FinBoxFourierNeg ell),
        cmp99SourceFlatPhysicalColumnGreenEndpointSample
          (cmp99FinBoxFourierNeg ell) 0 a x y k := by
      exact Equiv.sum_comp e _

end

end YangMills.RG
