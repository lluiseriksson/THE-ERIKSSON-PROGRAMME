import YangMills.RG.BalabanCMP89SourceNeumannRestrictedStraightPathEnergy

/-!
# Restricted parallel-defect bound for the CMP89 Neumann recursion

PRE-VALIDATION: source present; `.olean` not yet materialized and the result
has not yet been verified by the Lean compiler.

The pointwise CMP99 straight-transport estimate pays one factor `M` for the
length of each path.  The restricted straight-path theorem pays the second
factor `M` when all path layers are summed against the literal regional
Neumann energy.  Their composition is volume-free: no active-region
cardinality and no zero-extension boundary energy occur.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The restriction of the literal parallel-average defect to active coarse
bonds is controlled by `blockWeight * M²` times the raw fine regional
Neumann energy.  The two factors of `M` retain their distinct conventions:
one is path length and one counts path layers. -/
theorem norm_restrictOne_cmp99SourceParallelAverageDefectCochain_sq_le_raw
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖restrictOneCLM (𝔤 := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceParallelAverageDefectCochain rho U
          (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change
    (∑ b : ActiveGaugeRegion.Bond
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
      ‖cmp99SourceParallelAverageDefectValue rho U
        (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
          b.1.1 b.1.2‖ ^ 2) ≤ _
  calc
    (∑ b : ActiveGaugeRegion.Bond
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
      ‖cmp99SourceParallelAverageDefectValue rho U
        (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
          b.1.1 b.1.2‖ ^ 2) ≤
      ∑ b : ActiveGaugeRegion.Bond
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        cmp99SourceBlockAverageWeight M d * (M : ℝ) *
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1.1},
            covariantPathEnergy rho U
              (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
              (cmp99SourceParallelTransportPath (G := SUN Nc)
                x.1 b.1.2).edges := by
      gcongr with b _
      exact norm_cmp99SourceParallelAverageDefectValue_sq_le
        rho U (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
          b.1.1 b.1.2
    _ = cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ∑ i : CMP89SourceNeumannParallelStartIndex Omega,
          covariantPathEnergy rho U
            (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
            (cmp99SourceParallelTransportPath (G := SUN Nc)
              i.2.1 i.1.1.2).edges := by
      rw [Fintype.sum_sigma]
      simp only [← Finset.mul_sum]
    _ ≤ cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ((M : ℝ) *
          ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
        (sum_cmp89SourceNeumannParallelPathEnergy_le_raw Omega rho U phi)
      unfold cmp99SourceBlockAverageWeight
      positivity
    _ = cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
      ring

end

end YangMills.RG
