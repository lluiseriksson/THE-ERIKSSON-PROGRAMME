import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft
import tmp.BalabanCMP99PhysicalBackgroundRealSlice.draft
import YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Compact real slice of the analytic regional Laplacian

The analytic stencil of CMP99 (3.51)--(3.54) is compared with the literal
physical Dirichlet Laplacian already present in the source tower.  The
comparison is proved from zero extension, the one-link compact adjoint
identity and the explicit nearest-neighbour stencil; no Laplacian equality is
an input.  This is only the real-slice dictionary.  The complex local bound
(3.54), inverse/resolvent and four actions remain open.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Dirichlet extension commutes pointwise with the canonical physical-fibre
complexification. -/
theorem cmp99Eq360ComplexDirichletExtend_realSlice
    (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99Eq360ComplexDirichletExtend Omega
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      WithLp.toLp 2 fun x =>
        cmp99SUNLieCoordComplexificationLM Nc
          (extendZeroZeroCLM Omega phi x) := by
  ext x
  by_cases hx : x ∈ Omega.sites <;>
    simp [cmp99Eq360ComplexDirichletExtend, extendZeroZeroCLM, hx]

/-- The analytic forward difference restricts to the complexification of the
literal physical covariant difference, including the printed spacing. -/
theorem cmp99Eq360ComplexCovariantDifference_realSlice
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (phi : GaugeZeroCochain d N (SUNLieCoord Nc))
    (b : PhysicalBond d N) :
    cmp99Eq360ComplexCovariantDifference
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) spacing
        (WithLp.toLp 2 fun x =>
          cmp99SUNLieCoordComplexificationLM Nc (phi x)) b =
      cmp99SUNLieCoordComplexificationLM Nc
        (spacing⁻¹ • covariantD0CLM (matrixSUNAdjointModel Nc) U phi b) := by
  simp only [cmp99Eq360ComplexCovariantDifference,
    cmp99PhysicalGaugeBackgroundToSpecialLinear_apply,
    cmp99SpecialLinearAdjointCoordLM_realSlice]
  rw [covariantD0CLM_apply, map_smul, map_sub]
  norm_cast

/-- On every compact physical background the complete analytic regional
stencil is exactly the coordinate complexification of the physical
Dirichlet covariant Laplacian. -/
theorem cmp99Eq360ComplexRegionalLaplacian_realSlice
    (Omega : ActiveGaugeRegion d N)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99Eq360ComplexRegionalLaplacian Omega
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) spacing
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) x =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) U spacing phi x) := by
  rw [cmp99Eq360ComplexRegionalLaplacian_apply,
    cmp99Eq360ComplexDirichletExtend_realSlice,
    cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  change _ = cmp99SUNLieCoordComplexificationLM Nc
    (cmp99GeneratedAmbientScaledCovariantLaplacian
      (matrixSUNAdjointModel Nc) U spacing
      (extendZeroZeroCLM Omega phi) x.1)
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply]
  rw [map_smul, map_sum]
  have hspacing : ((spacing⁻¹ : ℝ) : ℂ) = (spacing : ℂ)⁻¹ := by
    norm_cast
  rw [← hspacing, Complex.coe_smul]
  apply congrArg ((spacing⁻¹ : ℝ) • ·)
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_sub]
  rw [cmp99Eq360ComplexCovariantDifference_realSlice]
  rw [cmp99Eq360ComplexCovariantDifference_realSlice]
  rw [cmp99PhysicalGaugeBackgroundToSpecialLinear_apply]
  rw [cmp99SpecialLinearAdjointCoordLM_realSlice_inv]
  norm_cast

end

end YangMills.RG
