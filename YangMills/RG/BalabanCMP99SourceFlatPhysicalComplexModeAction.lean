/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport
import YangMills.RG.BalabanCMP99SourceFlatQprimeComplexFibreModeAction

/-!
# PRE-VALIDATION: active flat physical average on complex Fourier modes

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

The literal physical CMP99 average is real-linear on the real Lie-coordinate
fibre.  This module constructs its pointwise coordinate complexification and,
separately, the source-normalized active average on the explicit complexified
fibre with identity transport.  It proves that the two commute in the flat
background.  Reindexing each complete active owner block by its canonical
internal offsets then transfers the sealed one-block Fourier calculation to
the actual active-region CLM.

Honest scope: this does not identify an interacting contour transport with
the flat one, construct a global Fourier equivalence, identify the source
weighted adjoint on Fourier coefficients, construct an inverse or produce a
regional Green bound.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Pointwise coordinate complexification on an active zero-cochain. -/
noncomputable def cmp99ActiveGaugeZeroCochainComplexificationCLM
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi => WithLp.toLp 2 fun x =>
        cmp99SUNLieCoordComplexificationLM Nc (phi x)
      map_add' := fun phi psi => by
        apply WithLp.ofLp_injective
        funext x
        exact (cmp99SUNLieCoordComplexificationLM Nc).map_add (phi x) (psi x)
      map_smul' := fun r phi => by
        apply WithLp.ofLp_injective
        funext x
        exact (cmp99SUNLieCoordComplexificationLM Nc).map_smul r (phi x) }

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99ActiveGaugeZeroCochainComplexificationCLM_apply
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi x =
      cmp99SUNLieCoordComplexificationLM Nc (phi x) := rfl

/-- Identity transport on the explicit complexified physical fibre. -/
def cmp99SourceFlatComplexTransport :
    FinBox d N' → FinBox d (M * N') →
      (SUNLieComplexCoord Nc ≃ₗᵢ[ℝ] SUNLieComplexCoord Nc) :=
  fun _ _ => LinearIsometryEquiv.refl ℝ (SUNLieComplexCoord Nc)

omit [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatComplexTransport_apply
    (y : FinBox d N') (x : FinBox d (M * N'))
    (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatComplexTransport y x v = v := rfl

/-- The source-normalized active average on the explicit complexified fibre,
with the flat transport constructed rather than supplied by a caller. -/
noncomputable def cmp99SourceFlatComplexBlockAverageCLM
    (Omega : ActiveGaugeRegion d (M * N')) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieComplexCoord Nc) :=
  cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceFlatComplexTransport (d := d) (M := M) (N' := N') (Nc := Nc))

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatComplexBlockAverageCLM_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    cmp99SourceFlatComplexBlockAverageCLM Omega phi y =
      cmp99SourceBlockAverageWeight M d •
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          phi (cmp99ActiveFineSiteOfBlock Omega y x) := by
  rfl

/-- Complexifying the literal physical flat average pointwise is exactly the
same as first complexifying the field and then using identity transport in
the explicit complexified fibre. -/
theorem cmp99SourceFlatComplexBlockAverage_commutes_complexification
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99SourceFlatComplexBlockAverageCLM Omega
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho
            (cmp99SourceFlatGaugeConfig d (M * N') Nc)) phi) := by
  apply WithLp.ofLp_injective
  funext y
  change cmp99SourceFlatComplexBlockAverageCLM Omega
      (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) y =
    cmp99SUNLieCoordComplexificationLM Nc
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho
          (cmp99SourceFlatGaugeConfig d (M * N') Nc)) phi y)
  rw [cmp99SourceFlatComplexBlockAverageCLM_apply,
    cmp99SourceTransportedBlockAverageCLM_flat_apply, map_smul, map_sum]
  simp only [cmp99ActiveGaugeZeroCochainComplexificationCLM_apply]

/-- Restriction of one explicit complex-fibre Fourier mode to an active
region.  No Fourier family or enumeration is supplied. -/
def cmp99SourceFlatActiveComplexFibreFourierMode
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (k : FinBox d N) (v : SUNLieComplexCoord Nc) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun x => cmp99FlatComplexFibreFourierMode k v x.1

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatActiveComplexFibreFourierMode_apply
    {N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (k : FinBox d N) (v : SUNLieComplexCoord Nc)
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99SourceFlatActiveComplexFibreFourierMode Omega k v x =
      cmp99FlatComplexFibreFourierMode k v x.1 := rfl

omit [NeZero Nc] in
/-- Exact action of the actual active-region flat complex average on one
fine Fourier mode.  The target is the restriction of the internally
constructed coarse reciprocal alias mode. -/
theorem cmp99SourceFlatComplexBlockAverage_fourierMode
    (Omega : ActiveGaugeRegion d (M * N'))
    (k : FinBox d (M * N')) (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatComplexBlockAverageCLM Omega
        (cmp99SourceFlatActiveComplexFibreFourierMode Omega k v) =
      cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum k) •
        cmp99SourceFlatActiveComplexFibreFourierMode
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
          (cmp99SourceFlatQprimeCoarseAlias k) v := by
  apply WithLp.ofLp_injective
  funext y
  rw [cmp99SourceFlatComplexBlockAverageCLM_apply]
  rw [sum_blockSites_eq_sum_offsets y.1]
  simpa only [cmp99SourceFlatComplexTransport_apply,
    cmp99SourceFlatActiveComplexFibreFourierMode_apply,
    cmp99ActiveFineSiteOfBlock_val, cmp99BlockOffsetEquiv,
    RCLike.real_smul_eq_coe_smul] using
    (cmp99SourceFlatQprimeWeightedBlockSum_complexFibreFourierMode_eq_coarseAlias
      k y.1 v)

end

end YangMills.RG
