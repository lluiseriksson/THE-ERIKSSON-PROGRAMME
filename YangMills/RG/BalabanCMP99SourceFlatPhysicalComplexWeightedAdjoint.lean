/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction

/-!
# PRE-VALIDATION: flat physical complex weighted adjoint

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

The printed CMP99 weighted adjoint has coefficient one between the source
lattice-spacing Hilbert products.  This module constructs that synthesis on
the explicit complexified physical fibre with the already sealed identity
flat transport.  It proves commutation with pointwise complexification of the
literal physical adjoint and records its exact pointwise action on a coarse
Fourier mode.

Honest scope: the endpoint is a pointwise owner-site synthesis identity.  It
does not construct a global Fourier equivalence or identify the synthesized
field with the direct-momentum column on a fixed reciprocal fibre.  It also
does not replace interacting transport by flat transport, construct an
inverse or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The source weighted adjoint on the explicit complex physical fibre,
with coefficient one and internally fixed flat identity transport. -/
noncomputable def cmp99SourceFlatComplexBlockWeightedAdjointCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieComplexCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
    (cmp99SourceFlatComplexTransport
      (d := d) (M := M) (N' := N') (Nc := Nc))

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega eta x =
      eta ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega (blockSite M N' x.1)).2
            (hOmega x.1 x.2)⟩ := by
  rw [cmp99SourceFlatComplexBlockWeightedAdjointCLM,
    cmp99SourceTransportedBlockWeightedAdjointCLM,
    cmp99TransportedBlockSynthesisCLM_apply]
  simp only [one_smul]
  rfl

/-- Complexifying the literal physical flat weighted adjoint pointwise is
the same as applying the internally constructed complex synthesis. -/
theorem cmp99SourceFlatComplexBlockWeightedAdjoint_commutes_complexification
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (rho : SUNAdjointModel Nc)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
        (cmp99ActiveGaugeZeroCochainComplexificationCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) eta) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
          (cmp99SourceWeightedPhysicalTransport rho
            (cmp99SourceFlatGaugeConfig d (M * N') Nc)) eta) := by
  apply WithLp.ofLp_injective
  funext x
  rw [cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply]
  change cmp99SUNLieCoordComplexificationLM Nc
      (eta ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega (blockSite M N' x.1)).2
            (hOmega x.1 x.2)⟩) =
    cmp99SUNLieCoordComplexificationLM Nc
      (cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) eta x)
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_flat_apply]

/-- Pointwise fine-region field obtained by synthesizing one coarse complex
Fourier mode.  This is not yet a statement about fine Fourier coefficients. -/
def cmp99SourceFlatActiveComplexCoarseModeSynthesis
    (Omega : ActiveGaugeRegion d (M * N'))
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun x =>
    cmp99FlatComplexFibreFourierMode ell v (blockSite M N' x.1)

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatActiveComplexCoarseModeSynthesis_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc)
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99SourceFlatActiveComplexCoarseModeSynthesis Omega ell v x =
      cmp99FlatComplexFibreFourierMode ell v (blockSite M N' x.1) := rfl

omit [NeZero d] [NeZero Nc] in
/-- Exact pointwise action of the complex source weighted adjoint on one
restricted coarse Fourier mode.  No reciprocal-fibre expansion is asserted. -/
theorem cmp99SourceFlatComplexBlockWeightedAdjoint_fourierMode
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceFlatActiveComplexFibreFourierMode
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) ell v) =
      cmp99SourceFlatActiveComplexCoarseModeSynthesis Omega ell v := by
  apply WithLp.ofLp_injective
  funext x
  rw [cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply]
  rfl

end

end YangMills.RG
