import YangMills.RG.BalabanCMP89SourceNeumannKernelAbsorption
import YangMills.RG.BalabanCMP89SourceNeumannRecursiveDefectBound
import YangMills.RG.BalabanCMP89SourceNeumannOneScaleRange
import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare

/-!
# One quantitative CMP89 Neumann recursion step

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

On the fine Neumann kernel, the source-normalized average is reconstructed by
the unit synthesis.  Its counting norm therefore pays exactly `M^d`, while
the quantitative transport defect pays `M^{-d}`.  This leaf exposes their
exact cancellation and feeds the resulting volume-free coefficient into the
regional kernel-absorption theorem.

The next coarse averaging operator and its Poincare estimate remain visible
inputs.  Identifying them with consecutive prefixes of the generated retained
tower is a separate dictionary; no recursive family is smuggled into this
one-step statement.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal volume-free coefficient left after `M^{-d}` in the block
average cancels `M^d` in the exact synthesis norm. -/
noncomputable def cmp89SourceNeumannOneStepDefectCoefficient
    (spacing epsilonFine epsilonCoarse : ℝ) : ℝ :=
  ‖(((M : ℝ) * spacing)⁻¹)‖ ^ 2 *
    (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
      epsilonCoarse)) ^ 2 * (d : ℝ)

/-- The coarse average of a fine Neumann-kernel field has a normalized
coarse derivative bounded by the volume-free one-step defect coefficient.
The equality `M^{-d} * M^d = 1` is used explicitly in the proof. -/
theorem norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega (matrixSUNAdjointModel Nc) U spacing phi = 0)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    let psi := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) phi
    ‖cmp89SourceNeumannRegionalCovariantD0CLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (matrixSUNAdjointModel Nc) V ((M : ℝ) * spacing) psi‖ ^ 2 ≤
      cmp89SourceNeumannOneStepDefectCoefficient
        (d := d) (M := M) spacing epsilonFine epsilonCoarse * ‖psi‖ ^ 2 := by
  let OmegaC := cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
  let psi := cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) phi
  have hext :
      cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U
          (extendZeroZeroCLM Omega phi) =
        extendZeroZeroCLM OmegaC psi := by
    simpa only [OmegaC, psi] using
      cmp99FullSourceBlockAverage_extendZero_eq
        Omega hOmega (matrixSUNAdjointModel Nc) U phi
  have hrestricted :
      restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
          (covariantD0CLM (matrixSUNAdjointModel Nc) V
            (extendZeroZeroCLM OmegaC psi)) =
        restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
          (cmp99SourceCoarseTransportRemainderCochain
            (matrixSUNAdjointModel Nc) U V (extendZeroZeroCLM Omega phi)) := by
    rw [← hext]
    simpa only [OmegaC] using
      restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel
        Omega (matrixSUNAdjointModel Nc) U V hspacing phi hD
  have hrem :=
    norm_restrictOne_cmp99SourceCoarseTransportRemainderCochain_sq_le
      Omega U V phi epsilonFine epsilonCoarse epsilonFine_nonneg
      epsilonCoarse_nonneg fine_small coarse_small
  have hrange :=
    cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average
      Omega hOmega (matrixSUNAdjointModel Nc) U hspacing phi hD
  have hnorm :=
    norm_cmp99SourceTransportedBlockWeightedAdjointCLM_sq
      Omega hOmega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) psi
  rw [hrange] at hnorm
  change ‖(((M : ℝ) * spacing)⁻¹) •
      restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
        (covariantD0CLM (matrixSUNAdjointModel Nc) V
          (extendZeroZeroCLM OmegaC psi))‖ ^ 2 ≤ _
  rw [hrestricted, norm_smul]
  calc
    (‖((M : ℝ) * spacing)⁻¹‖ *
        ‖restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
          (cmp99SourceCoarseTransportRemainderCochain
            (matrixSUNAdjointModel Nc) U V
              (extendZeroZeroCLM Omega phi))‖) ^ 2 ≤
      ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
        (cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hrem (sq_nonneg _)
    _ = ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) * ‖psi‖ ^ 2 := by
      rw [hnorm]
      have hweight := cmp99SourceBlockAverageWeight_mul_card
        (d := d) (M := M)
      calc
        ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
            (cmp99SourceBlockAverageWeight M d *
              (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
                epsilonCoarse)) ^ 2 * (d : ℝ) *
                  ((M : ℝ) ^ d * ‖psi‖ ^ 2)) =
          ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
            (cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ d) *
              (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
                epsilonCoarse)) ^ 2 * (d : ℝ) * ‖psi‖ ^ 2 := by ring
        _ = _ := by rw [hweight]; ring
    _ = _ := rfl

/-- One physical recursion step.  A vanishing fine Neumann derivative and a
vanishing next coarse average imply exact vanishing once the displayed
one-step coefficient lies below the coarse Poincare threshold. -/
theorem eq_zero_of_cmp89SourceNeumann_oneStep_absorption
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (Qnext : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) →L[ℝ] F)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (CP : ℝ) (hCP : 0 < CP)
    (hP : CMP89SourceNeumannRegionalPoincare
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (matrixSUNAdjointModel Nc) V Qnext ((M : ℝ) * spacing) CP)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega (matrixSUNAdjointModel Nc) U spacing phi = 0)
    (hQ : Qnext
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U)
          phi) = 0)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse)
    (hsmall : CP * cmp89SourceNeumannOneStepDefectCoefficient
      (d := d) (M := M) spacing epsilonFine epsilonCoarse < 1) :
    phi = 0 := by
  let OmegaC := cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
  let psi := cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) phi
  have hpsi : psi = 0 :=
    eq_zero_of_cmp89SourceNeumannRegionalPoincare_of_derivative_sq_le
      OmegaC (matrixSUNAdjointModel Nc) V Qnext ((M : ℝ) * spacing) CP
      (cmp89SourceNeumannOneStepDefectCoefficient
        (d := d) (M := M) spacing epsilonFine epsilonCoarse)
      hCP hP psi hQ
      (norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le
        Omega hOmega U V hspacing phi hD epsilonFine epsilonCoarse
        epsilonFine_nonneg epsilonCoarse_nonneg fine_small coarse_small)
      hsmall
  have hrange :=
    cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average
      Omega hOmega (matrixSUNAdjointModel Nc) U hspacing phi hD
  change cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U)
        psi = phi at hrange
  rw [hpsi, map_zero] at hrange
  exact hrange.symm

end

end YangMills.RG
