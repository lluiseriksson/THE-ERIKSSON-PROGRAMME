/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Exact termwise bridge from the D4 affine-residue derivative coefficients to
the physical source-minus-target raw `alpha = 0` integral.  The physical
Holder multiplier `xi^(-alpha)` remains a separate H5 brick.  This file
contains no operator bound, owner estimate, regional B0, window-15 claim or
terminal field.
-/

import YangMills.RG.BalabanCMP89Eq249MassUniformRealSliceRecombination
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization
import YangMills.RG.BalabanCMP116CMP89PhysicalBondDisplacementDictionary

namespace YangMills.RG

noncomputable section

/-- Adding the physical negative bond edge to the reindexed forward affine
residue recovers the source affine residue exactly. -/
theorem
    cmp99SourceSeparatedPhysicalBondHolder_add_forwardAffineResidue_eq_sourceAffineResidue_draft
    {K N : ℕ} [NeZero K] [NeZero N]
    (x : FinBox 4 (K * N)) (bondNu : Fin 4) (u n : Fin 4 → ℤ) :
    (fun nu =>
        cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu) nu +
          cmp89SignedLatticeResidueAffineMap K
            (cmp89Eq248FineLatticeForwardCoordinateShift bondNu u) n nu) =
      cmp89SignedLatticeResidueAffineMap K u n := by
  funext nu
  by_cases hnu : nu = bondNu
  · subst nu
    rw [cmp116CMP89PhysicalBondHolderDisplacement_apply]
    simp [cmp89SignedLatticeResidueAffineMap,
      cmp89Eq248FineLatticeForwardCoordinateShift]
  · rw [cmp116CMP89PhysicalBondHolderDisplacement_apply]
    simp [cmp89SignedLatticeResidueAffineMap,
      cmp89Eq248FineLatticeForwardCoordinateShift, hnu]

/-- One source-normalized raw `alpha = 0` integral is exactly source
coefficient minus the target coefficient after D4's seam-safe residue
reindexing.  The sign is forced by the physical convention
`source - target = -e_bondNu`; the derivative direction remains the
independent index `derivMu`. -/
theorem
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral_physicalBond_eq_sourceCoefficient_sub_forwardCoefficient_draft
    {K N : ℕ} [NeZero K] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (x : FinBox 4 (K * N)) (derivMu bondNu : Fin 4) (u : Fin 4 → ℤ)
    (n : CMP99FlatIntegerResidueClass 4 N 0) :
    let forwardU := cmp89Eq248FineLatticeForwardCoordinateShift bondNu u
    let transportU := cmp89SignedLatticeResidueAffineMap K forwardU n.1
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral K 1 mass a derivMu
        (cmp116CMP89PhysicalBondHolderDisplacement (x, bondNu)) transportU =
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 mass a derivMu u n.1 -
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 mass a derivMu forwardU n.1 := by
  dsimp only
  have hsum :=
    cmp99SourceSeparatedPhysicalBondHolder_add_forwardAffineResidue_eq_sourceAffineResidue_draft
      (K := K) (N := N) x bondNu u n.1
  rw [
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_fourierLeftDerivativeDiff_massUniform_draft
      (L := K) (j := 1) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass derivMu]
  unfold cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
  rw [hsum]

end

end YangMills.RG
