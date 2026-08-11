/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionStabilizedParticularSolution

/-!
# Central-stabilized flat physical `G Q'^*` field

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

An arbitrary coarse complex physical field is decomposed by the already
sealed finite `FinBox` DFT.  Every coarse Fourier coefficient is fed to the
internally constructed central-stabilized one-mode particular solution, and
the resulting finite sum is an actual full-box fine field.  Additivity of the
literal precision and the exact inverse DFT then give `K H eta = Q'^* eta`.

The weighted adjoint in the conclusion is the actual coefficient-one flat
physical weighted adjoint specialized to the full fine box.  No inverse
operator, solution family or Fourier reconstruction identity is supplied by
a caller.  Packaging as an inverse CLM, identification by inverse uniqueness
with the generated physical covariance, regional transport and a uniform
physical `B0` remain downstream obligations.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- The physical-fibre inverse DFT is the literal finite Fourier sum with
the sealed inverse-volume normalization. -/
theorem cmp99FlatPhysicalFibreInvDFT_eq_fourierSum
    {N : ℕ} [NeZero N]
    (psi : FinBox d N → SUNLieComplexCoord Nc) :
    cmp99FlatPhysicalFibreInvDFT psi =
      ∑ k : FinBox d N,
        cmp99FlatComplexFibreFourierMode k
          (((N : ℂ) ^ d)⁻¹ • psi k) := by
  funext x
  ext b
  change
    ((N : ℂ) ^ d)⁻¹ *
        ∑ k : CMP99FlatZModBox d N,
          cmp99FlatZModFourierCharacter k (cmp99FinBoxZModEquiv d N x) *
            psi ((cmp99FinBoxZModEquiv d N).symm k) b =
      ∑ k : FinBox d N,
        cmp99FlatFourierMode k x *
          (((N : ℂ) ^ d)⁻¹ * psi k b)
  rw [← Equiv.sum_comp (cmp99FinBoxZModEquiv d N)]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← cmp99FlatFourierMode_eq_finBoxFourierCharacter]
  ring

omit [NeZero d] [NeZero Nc] in
/-- Exact finite Fourier expansion of an arbitrary coarse physical-fibre
field. -/
theorem cmp99FlatPhysicalFibre_fourierSum_DFT
    {N : ℕ} [NeZero N]
    (eta : FinBox d N → SUNLieComplexCoord Nc) :
    (∑ k : FinBox d N,
        cmp99FlatComplexFibreFourierMode k
          (((N : ℂ) ^ d)⁻¹ • cmp99FlatPhysicalFibreDFT eta k)) = eta := by
  rw [← cmp99FlatPhysicalFibreInvDFT_eq_fourierSum]
  exact cmp99FlatPhysicalFibreInvDFT_DFT eta

/-- Canonical restriction of a full coarse complex physical field to the
coarse active region induced by the full fine box. -/
def cmp99SourceFlatFullActiveComplexCoarseField
    (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N')
        (cmp99SourceFlatFullFineRegion d (M * N')))
      (SUNLieComplexCoord Nc) :=
  WithLp.toLp 2 fun y => eta y.1

/-- The actual coefficient-one flat physical weighted adjoint on an arbitrary
full coarse complex field. -/
noncomputable def cmp99SourceFlatFullComplexWeightedAdjoint
    (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  fun x =>
    cmp99SourceFlatComplexBlockWeightedAdjointCLM
      (cmp99SourceFlatFullFineRegion d (M * N'))
      (cmp99SourceFlatFullFineRegion_blockSaturated
        (d := d) (M := M) (N' := N'))
      (cmp99SourceFlatFullActiveComplexCoarseField eta)
      ⟨x, mem_cmp99SourceFlatFullFineRegion_sites x⟩

omit [NeZero d] [NeZero Nc] in
@[simp] theorem cmp99SourceFlatFullComplexWeightedAdjoint_apply
    (eta : FinBox d N' → SUNLieComplexCoord Nc)
    (x : FinBox d (M * N')) :
    cmp99SourceFlatFullComplexWeightedAdjoint eta x =
      eta (blockSite M N' x) := by
  rw [cmp99SourceFlatFullComplexWeightedAdjoint,
    cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply]
  rfl

omit [NeZero d] [NeZero Nc] in
/-- The arbitrary-source weighted adjoint specializes exactly to the sealed
one-mode physical weighted-adjoint field. -/
theorem cmp99SourceFlatFullComplexWeightedAdjoint_fourierMode
    (ell : FinBox d N') (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexWeightedAdjoint
        (cmp99FlatComplexFibreFourierMode ell v) =
      cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v := by
  funext x
  rw [cmp99SourceFlatFullComplexWeightedAdjoint_apply,
    cmp99SourceFlatFullComplexWeightedAdjointCoarseMode_apply]

/-- Finite coarse-Fourier superposition of the internally constructed
central-stabilized one-mode particular solutions. -/
def cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
    (mass a : ℝ) (eta : FinBox d N' → SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  ∑ ell : FinBox d N',
    cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
      ell mass a
        ((((N' : ℕ) : ℂ) ^ d)⁻¹ • cmp99FlatPhysicalFibreDFT eta ell)

/-- Literal full-box equation `K H eta = Q'^* eta` for every coarse complex
physical source.  The field `H eta` is constructed internally by finite DFT
superposition; it is not supplied as a solution family. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_stabilizedQprimeStarField
    (mass a : ℝ) (eta : FinBox d N' → SUNLieComplexCoord Nc)
    (hfine : ∀ ell : FinBox d N',
      ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
            (d := d) (M := M) (N' := N') ell →
          cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized : ∀ ell : FinBox d N',
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarField
          mass a eta) =
      cmp99SourceFlatFullComplexWeightedAdjoint eta := by
  let coeff : FinBox d N' → SUNLieComplexCoord Nc :=
    fun ell => (((N' : ℕ) : ℂ) ^ d)⁻¹ •
      cmp99FlatPhysicalFibreDFT eta ell
  let term : FinBox d N' →
      FinBox d (M * N') → SUNLieComplexCoord Nc :=
    fun ell =>
      cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
        ell mass a (coeff ell)
  change cmp99SourceFlatFullComplexPrecisionAction mass a
      (∑ ell, term ell) = _
  have hprecisionSum :
      cmp99SourceFlatFullComplexPrecisionAction mass a (∑ ell, term ell) =
        ∑ ell, cmp99SourceFlatFullComplexPrecisionAction mass a (term ell) := by
    simpa only using
      cmp99SourceFlatFullComplexPrecisionAction_finset_sum
        (d := d) (M := M) (N' := N') (Nc := Nc)
        mass a Finset.univ term
  rw [hprecisionSum]
  calc
    (∑ ell, cmp99SourceFlatFullComplexPrecisionAction mass a (term ell)) =
        ∑ ell, cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
          ell (coeff ell) := by
      apply Finset.sum_congr rfl
      intro ell _
      exact
        cmp99SourceFlatFullComplexPrecisionAction_stabilizedParticularSolution
          ell mass a (coeff ell) (hfine ell) (hstabilized ell)
    _ = cmp99SourceFlatFullComplexWeightedAdjoint eta := by
      funext x
      rw [Finset.sum_apply,
        cmp99SourceFlatFullComplexWeightedAdjoint_apply]
      have hfourier := congrFun
        (cmp99FlatPhysicalFibre_fourierSum_DFT eta)
        (blockSite M N' x)
      simpa only [coeff,
        cmp99SourceFlatFullComplexWeightedAdjointCoarseMode_apply] using hfourier

end

end YangMills.RG
