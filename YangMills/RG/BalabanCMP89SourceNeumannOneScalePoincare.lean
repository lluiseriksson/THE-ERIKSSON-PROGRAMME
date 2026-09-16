import YangMills.RG.BalabanCMP89SourceNeumannOneScaleRange
import YangMills.RG.BalabanCMP89SourceNeumannRegionalPoincareExistence

/-!
# One-scale CMP89 Neumann Poincare producer

The exact range identity for the source-normalized physical block average
closes the literal one-scale joint kernel.  Finite-dimensional compactness
then produces a positive Neumann Poincare constant for that same average.

This is deliberately a one-scale result.  It neither identifies a recursive
retained prefix nor propagates the Neumann kernel through the generated
`Ubar` background chain.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The internal-bond Neumann derivative and the literal physical one-scale
average have trivial joint kernel. -/
theorem cmp89SourceNeumann_oneScale_jointKernel
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0) :
    CMP89SourceNeumannRegionalJointKernelTrivial Omega rho U
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U)) spacing := by
  intro phi hD hQ
  have hrange :=
    cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average
      Omega hOmega rho U hspacing phi hD
  rw [hQ, map_zero] at hrange
  exact hrange.symm

/-- Some positive Neumann Poincare constant exists for the same literal
one-scale physical average.  No uniform numerical bound is claimed. -/
theorem exists_cmp89SourceNeumann_oneScale_poincare
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0) :
    ∃ CP : ℝ, 0 < CP ∧
      CMP89SourceNeumannRegionalPoincare Omega rho U
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho U)) spacing CP := by
  exact exists_cmp89SourceNeumannRegionalPoincare_of_jointKernel
    Omega rho U
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U))
      spacing
      (cmp89SourceNeumann_oneScale_jointKernel
        Omega hOmega rho U hspacing)

end

end YangMills.RG
