/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesis

/-!
# Row-oriented sampled endpoint normal form

COLD-SEALED: the exact source checkpoint `62862316ed330ef0efa8db676fa3b3f97b441c6e`
was compiler verified from a cold checkout by GitHub Actions run
`31917596890`; the focal completed successfully with 8657 jobs and the
three-declaration audit printed exactly the standard axiom trio.

The cold-sealed finite Green synthesis carries the transpose solution, hence
the CMP89 row amplitude.  The preceding endpoint-phase dictionary identifies
the quotient of its fine Fourier character by the coarse character with the
literal signed-alias phase.  This file composes exactly those two statements:
one physical summand, and then the complete finite fibre sum, are put into a
row-oriented sampled endpoint normal form.

The orientation is deliberately part of the name.  This module does not
replace the row amplitude by the CMP89 column amplitude, reindex through
cross-fibre Fourier negation, identify the finite sum with a Brillouin
integral, construct regional `B0`, attain window 15, discharge a terminal
field, or inhabit `TermSource`.  In particular, it makes no termwise claim
that the distinguished zero alias is preserved by the affine carry; the later
orientation bridge must act on the complete finite sum.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- One literal signed-alias endpoint sample with the transposed CMP89
solution.  The phase and row-oriented coefficient remain separate factors. -/
def cmp99SourceFlatPhysicalTransposeGreenEndpointSample
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
        (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y))) *
    cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
      (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell k)

/-- Dividing one physical transpose-Green Fourier summand by its coarse mode
gives exactly the named row-oriented endpoint sample. -/
theorem cmp99SourceFlatPhysicalTransposeGreenFourierTerm_mul_coarseInv_eq_endpointSample
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (mass a : ℝ)
    (x : FinBox d (M * N')) (y : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99SourceFlatPhysicalTransposeGreenFourierTerm ell mass a x k *
        (cmp99FlatFourierMode ell y)⁻¹ =
      cmp99SourceFlatPhysicalTransposeGreenEndpointSample
        ell mass a x y k := by
  unfold cmp99SourceFlatPhysicalTransposeGreenFourierTerm
    cmp99SourceFlatPhysicalTransposeGreenEndpointSample
    cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
  calc
    (cmp99FlatFourierMode k.1 x *
          cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
              d M N' ell k)) *
        (cmp99FlatFourierMode ell y)⁻¹ =
      (cmp99FlatFourierMode k.1 x *
          (cmp99FlatFourierMode ell y)⁻¹) *
        cmp89Eq249StabilizedAliasTransposeSolution d M 1 mass a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) := by ring
    _ = _ := by
      rw [cmp99FlatFourierMode_div_coarseMode_eq_exp_entireAlias_endpoint]

/-- The complete normalized finite fibre sum is exactly the sum of the named
row-oriented endpoint samples.  No cardinality or integral normalization is
inserted. -/
theorem sum_cmp99SourceFlatPhysicalTransposeGreenFourierTerm_mul_coarseInv_eq_endpointSamples
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N') (mass a : ℝ)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenFourierTerm ell mass a x k) *
        (cmp99FlatFourierMode ell y)⁻¹ =
      ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatPhysicalTransposeGreenEndpointSample
          ell mass a x y k := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact
    cmp99SourceFlatPhysicalTransposeGreenFourierTerm_mul_coarseInv_eq_endpointSample
      ell mass a x y k

end

end YangMills.RG
