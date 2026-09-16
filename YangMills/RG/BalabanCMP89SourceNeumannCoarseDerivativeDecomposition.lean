import YangMills.RG.BalabanCMP89SourceNeumannRecursiveDefectBound

/-!
# Exact regional Neumann coarse-derivative decomposition

The full CMP99 coarse derivative already splits into a straight transported
defect and the explicit `Ubar` mismatch.  This file restricts that identity to
the active coarse Neumann bonds and restores the printed coarse lattice
spacing.  No norm estimate, smallness hypothesis or Dirichlet boundary term
is inserted.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The straight parallel component of the full coarse derivative, assembled
as a positive-bond cochain before regional restriction. -/
noncomputable def cmp99SourceParallelAverageDefectCochain
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    GaugeOneCochain d N' (SUNLieCoord Nc) :=
  WithLp.toLp 2 fun b =>
    cmp99SourceParallelAverageDefectValue rho U phi b.1 b.2

@[simp] theorem cmp99SourceParallelAverageDefectCochain_apply
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (b : PositiveBond d N') :
    cmp99SourceParallelAverageDefectCochain rho U phi b =
      cmp99SourceParallelAverageDefectValue rho U phi b.1 b.2 := rfl

/-- Restriction of the literal full coarse derivative is exactly restriction
of the sum of its two source-printed species. -/
theorem restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let OmegaC :=
      cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
        (covariantD0CLM rho V
          (cmp99FullSourceBlockAverage rho U
            (extendZeroZeroCLM Omega phi))) =
      restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
        (cmp99SourceParallelAverageDefectCochain rho U
            (extendZeroZeroCLM Omega phi) +
          cmp99SourceCoarseTransportRemainderCochain rho U V
            (extendZeroZeroCLM Omega phi)) := by
  dsimp only
  apply PiLp.ext
  intro b
  rcases b with ⟨⟨y, mu⟩, hb⟩
  change covariantD0CLM rho V
      (cmp99FullSourceBlockAverage rho U (extendZeroZeroCLM Omega phi))
        (y, mu) =
    cmp99SourceParallelAverageDefectValue rho U
        (extendZeroZeroCLM Omega phi) y mu +
      cmp99SourceCoarseTransportRemainder rho U V
        (extendZeroZeroCLM Omega phi) y mu
  exact covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder
    rho U V (extendZeroZeroCLM Omega phi) y mu

/-- The normalized coarse Neumann derivative of the literal transported
average, with the inverse coarse spacing outside the exact two-species sum. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_eq_twoSpecies
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let OmegaC :=
      cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    let Qfine := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport rho U)
    cmp89SourceNeumannRegionalCovariantD0CLM
        OmegaC rho V ((M : ℝ) * spacing) (Qfine phi) =
      (((M : ℝ) * spacing)⁻¹) •
        restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
          (cmp99SourceParallelAverageDefectCochain rho U
              (extendZeroZeroCLM Omega phi) +
            cmp99SourceCoarseTransportRemainderCochain rho U V
              (extendZeroZeroCLM Omega phi)) := by
  dsimp only
  rw [cmp89SourceNeumannRegionalCovariantD0CLM,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [← cmp99FullSourceBlockAverage_extendZero_eq
    Omega hOmega rho U phi]
  rw [restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder]

end

end YangMills.RG
