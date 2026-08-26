import YangMills.RG.BalabanCMP99SpecialUnitaryToSpecialLinearRealSlice
import YangMills.RG.BalabanCMP99ComplexTransportedBlockAverage
import YangMills.RG.BalabanCMP99SourceFlatPhysicalComplexModeAction

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# One-scale real slice of the analytic CMP99 average and printed star

The complex holonomy is constructed pointwise from the supplied physical
`SUN` holonomy.  The forward comparison keeps the printed `M^{-d}` mass, and
the starred comparison keeps the unit synthesis mass.  No `SL` family or
transport equality is supplied by the caller.
-/

namespace YangMills.RG

noncomputable section

variable {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]

/-- Canonical complex holonomy obtained from a physical compact holonomy. -/
def cmp99SUNHolonomyToSpecialLinear
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc) :
    FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  fun y x ↦ cmp99SUNToSpecialLinear Nc (holonomy y x)

@[simp] theorem cmp99SUNHolonomyToSpecialLinear_apply
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (y : FinBox d N') (x : FinBox d (M * N')) :
    cmp99SUNHolonomyToSpecialLinear holonomy y x =
      cmp99SUNToSpecialLinear Nc (holonomy y x) := rfl

/-- Pointwise complexification commutes with the literal source-normalized
one-scale average. -/
theorem cmp99ComplexAdjointBlockAverageCLM_realSlice
    (Omega : ActiveGaugeRegion d (M * N'))
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99ComplexAdjointBlockAverageCLM Omega
        (cmp99SUNHolonomyToSpecialLinear holonomy)
        (cmp99ActiveGaugeZeroCochainComplexificationCLM Omega phi) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99AdjointBlockAverageCLM Omega
          (cmp99SourceBlockAverageWeight M d)
          (matrixSUNAdjointModel Nc) holonomy phi) := by
  apply WithLp.ofLp_injective
  funext y
  unfold cmp99ComplexAdjointBlockAverageCLM
  rw [cmp99ComplexTransportedBlockAverageCLM_apply]
  change
    (cmp99SourceBlockAverageWeight M d : ℂ) •
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          cmp99SpecialLinearAdjointCoordLM
            (cmp99SUNToSpecialLinear Nc (holonomy y.1 x.1))
            (cmp99SUNLieCoordComplexificationLM Nc
              (phi (cmp99ActiveFineSiteOfBlock Omega y x))) =
      cmp99SUNLieCoordComplexificationLM Nc
        (cmp99AdjointBlockAverageCLM Omega
          (cmp99SourceBlockAverageWeight M d)
          (matrixSUNAdjointModel Nc) holonomy phi y)
  rw [cmp99AdjointBlockAverageCLM, cmp99TransportedBlockAverageCLM_apply,
    map_smul, map_sum]
  apply congrArg (fun Z ↦ (cmp99SourceBlockAverageWeight M d : ℂ) • Z)
  apply Finset.sum_congr rfl
  intro x _
  exact cmp99SpecialLinearAdjointCoordLM_realSlice
    (g := holonomy y.1 x.1)
    (phi (cmp99ActiveFineSiteOfBlock Omega y x))

/-- Pointwise complexification commutes with the independently constructed
printed-star synthesis.  The physical coefficient is literally one. -/
theorem cmp99ComplexAdjointBlockStarSynthesisCLM_realSlice
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega
        (cmp99SUNHolonomyToSpecialLinear holonomy)
        (cmp99ActiveGaugeZeroCochainComplexificationCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) eta) =
      cmp99ActiveGaugeZeroCochainComplexificationCLM Omega
        (cmp99AdjointBlockSynthesisCLM Omega hOmega 1
          (matrixSUNAdjointModel Nc) holonomy eta) := by
  apply WithLp.ofLp_injective
  funext x
  unfold cmp99ComplexAdjointBlockStarSynthesisCLM
  rw [cmp99ComplexTransportedBlockStarSynthesisCLM_apply]
  change cmp99SpecialLinearAdjointCoordLM
      (cmp99SUNToSpecialLinear Nc
        (holonomy (blockSite M N' x.1) x.1))⁻¹
      (cmp99SUNLieCoordComplexificationLM Nc
        (eta ⟨blockSite M N' x.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := N') Omega (blockSite M N' x.1)).2
              (hOmega x.1 x.2)⟩)) =
    cmp99SUNLieCoordComplexificationLM Nc
      (cmp99AdjointBlockSynthesisCLM Omega hOmega 1
        (matrixSUNAdjointModel Nc) holonomy eta x)
  rw [cmp99AdjointBlockSynthesisCLM,
    cmp99TransportedBlockSynthesisCLM_apply, one_smul]
  exact cmp99SpecialLinearAdjointCoordLM_realSlice_inv
    (g := holonomy (blockSite M N' x.1) x.1)
    (eta ⟨blockSite M N' x.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega (blockSite M N' x.1)).2
          (hOmega x.1 x.2)⟩)

end

end YangMills.RG
