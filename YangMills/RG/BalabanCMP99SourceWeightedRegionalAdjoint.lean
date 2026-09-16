/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalAdjoint

/-!
# The printed lattice-spacing adjoint for the CMP99 regional average

CMP99 (3.19), printed p. 393, fixes the one-step coefficient to `L^{-d}`.
The scalar product on a lattice of spacing `eta` is simultaneously fixed to
`eta^d` times the counting inner product.  Consequently the adjoint between
the fine spacing `eta` and coarse spacing `L eta` is the *unit-coefficient*
synthesis, not the counting-space adjoint carrying another factor `L^{-d}`.

This file records that convention directly.  It proves the weighted pairing
identity and the exact coisometry `Q Q^dagger = I`.  Thus the factor
`w^2 M^d` from the unweighted helper is not reused as a source normalization.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']
variable {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- The literal coefficient `L^{-d}` in CMP99 (3.19), with `M` denoting the
one-step lattice ratio. -/
noncomputable def cmp99SourceBlockAverageWeight (M d : ℕ) : ℝ :=
  ((M : ℝ) ^ d)⁻¹

theorem cmp99SourceBlockAverageWeight_mul_card :
    cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ d = 1 := by
  rw [cmp99SourceBlockAverageWeight, inv_mul_cancel₀]
  exact pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne M))

theorem card_mul_cmp99SourceBlockAverageWeight :
    (M : ℝ) ^ d * cmp99SourceBlockAverageWeight M d = 1 := by
  rw [mul_comm, cmp99SourceBlockAverageWeight_mul_card]

/-- Source-weighted `L²` pairing at lattice spacing `spacing`. -/
def cmp99SourceSpacingPairing {E : Type*} [Inner ℝ E]
    (d : ℕ) (spacing : ℝ) (x y : E) : ℝ :=
  spacing ^ d * inner ℝ x y

/-- The literal one-step average of CMP99 (3.19). -/
noncomputable def cmp99SourceTransportedBlockAverageCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g :=
  cmp99TransportedBlockAverageCLM Omega
    (cmp99SourceBlockAverageWeight M d) transport

/-- The source Hilbert adjoint: inverse transport with coefficient one. -/
noncomputable def cmp99SourceTransportedBlockWeightedAdjointCLM
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g →L[ℝ]
      ActiveGaugeZeroCochain Omega g :=
  cmp99TransportedBlockSynthesisCLM Omega hOmega 1 transport

/-- Relation to the counting-space Hilbert adjoint.  The factor `M^d` is
exactly the Radon--Nikodym ratio between coarse and fine lattice-spacing
inner products. -/
theorem cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega transport =
      ((M : ℝ) ^ d) •
        (cmp99SourceTransportedBlockAverageCLM Omega transport).adjoint := by
  rw [cmp99SourceTransportedBlockAverageCLM,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega
      (cmp99SourceBlockAverageWeight M d) transport]
  apply ContinuousLinearMap.ext
  intro eta
  ext x
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM,
    cmp99TransportedBlockSynthesisCLM_apply]
  let z : g := (transport (blockSite M N' x.1) x.1).symm
    (eta ⟨blockSite M N' x.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega (blockSite M N' x.1)).2
          (hOmega x.1 x.2)⟩)
  change (1 : ℝ) • z =
    (M : ℝ) ^ d • (cmp99SourceBlockAverageWeight M d • z)
  simp only [one_smul, smul_smul]
  rw [card_mul_cmp99SourceBlockAverageWeight, one_smul]

/-- Exact adjoint identity for the two printed Hilbert scalar products. -/
theorem cmp99SourceTransportedBlock_weightedAdjoint_pairing
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (spacing : ℝ) (phi : ActiveGaugeZeroCochain Omega g)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    cmp99SourceSpacingPairing d ((M : ℝ) * spacing)
        (cmp99SourceTransportedBlockAverageCLM Omega transport phi) eta =
      cmp99SourceSpacingPairing d spacing phi
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport eta) := by
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint]
  simp only [cmp99SourceSpacingPairing, mul_pow,
    ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [ContinuousLinearMap.adjoint_inner_right]
  ring

/-- With the printed coefficient and weighted adjoint, one scale is an exact
coisometry. -/
theorem cmp99SourceTransportedBlockAverage_comp_weightedAdjoint
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99SourceTransportedBlockAverageCLM Omega transport).comp
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) := by
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint]
  apply ContinuousLinearMap.ext
  intro eta
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, ContinuousLinearMap.id_apply]
  have hQ := congrArg
    (fun A : ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g →L[ℝ]
        ActiveGaugeZeroCochain
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g => A eta)
    (cmp99TransportedBlockAverage_comp_synthesis Omega hOmega
      (cmp99SourceBlockAverageWeight M d) transport)
  rw [cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega
      (cmp99SourceBlockAverageWeight M d) transport] at hQ
  change cmp99SourceTransportedBlockAverageCLM Omega transport
      ((cmp99SourceTransportedBlockAverageCLM Omega transport).adjoint eta) =
    (((cmp99SourceBlockAverageWeight M d) ^ 2 * (M : ℝ) ^ d) •
      ContinuousLinearMap.id ℝ _) eta at hQ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hQ
  rw [hQ, smul_smul]
  have hcoeff :
      (M : ℝ) ^ d *
          ((cmp99SourceBlockAverageWeight M d) ^ 2 * (M : ℝ) ^ d) = 1 := by
    rw [pow_two]
    calc
      (M : ℝ) ^ d *
          (cmp99SourceBlockAverageWeight M d *
            cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ d) =
        ((M : ℝ) ^ d * cmp99SourceBlockAverageWeight M d) *
          (cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ d) := by ring
      _ = 1 := by
        rw [card_mul_cmp99SourceBlockAverageWeight,
          cmp99SourceBlockAverageWeight_mul_card, one_mul]
  rw [hcoeff, one_smul]

/-- Counting-norm size of the source weighted adjoint.  The factor `M^d`
is precisely cancelled by the change from fine spacing `spacing` to coarse
spacing `M * spacing`. -/
theorem norm_cmp99SourceTransportedBlockWeightedAdjointCLM_sq
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    ‖cmp99SourceTransportedBlockWeightedAdjointCLM
        Omega hOmega transport eta‖ ^ 2 =
      (M : ℝ) ^ d * ‖eta‖ ^ 2 := by
  simpa only [cmp99SourceTransportedBlockWeightedAdjointCLM, one_pow,
    one_mul] using
    (norm_cmp99TransportedBlockSynthesisCLM_sq
      Omega hOmega 1 transport eta)

/-- Exact equality of the weighted norm squares at the two printed lattice
spacings. -/
theorem cmp99SourceTransportedBlockWeightedAdjoint_spacingNormSq
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (spacing : ℝ)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    spacing ^ d *
        ‖cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport eta‖ ^ 2 =
      ((M : ℝ) * spacing) ^ d * ‖eta‖ ^ 2 := by
  rw [norm_cmp99SourceTransportedBlockWeightedAdjointCLM_sq, mul_pow]
  ring

/-- The norm associated with the source lattice-spacing pairing. -/
noncomputable def cmp99SourceSpacingNorm {E : Type*} [Norm E]
    (d : ℕ) (spacing : ℝ) (x : E) : ℝ :=
  Real.sqrt (spacing ^ d * ‖x‖ ^ 2)

/-- The source weighted adjoint is an exact isometry between the coarse and
fine lattice-spacing norms. -/
theorem cmp99SourceTransportedBlockWeightedAdjoint_spacingNorm
    (Omega : ActiveGaugeRegion d (M * N')) (hOmega : Omega.BlockSaturated)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (spacing : ℝ)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    cmp99SourceSpacingNorm d spacing
        (cmp99SourceTransportedBlockWeightedAdjointCLM
          Omega hOmega transport eta) =
      cmp99SourceSpacingNorm d ((M : ℝ) * spacing) eta := by
  rw [cmp99SourceSpacingNorm, cmp99SourceSpacingNorm,
    cmp99SourceTransportedBlockWeightedAdjoint_spacingNormSq]

end

end YangMills.RG
