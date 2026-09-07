/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassOutputRow
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecisionDirectWeightedRow

/-!
# CMP99 fixed-output row of the generated physical precision

This module places the two literal summands of the generated precision in the
orientation printed in CMP99 (3.88): the output is fixed and input sites are
summed.  The covariant Laplacian is bounded directly from its one-link range;
the normalized `Q'^*Q'` term uses its physical block-isometry theorem.  The
two amplitudes remain separate until the final literal addition.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Direct fixed-output row of the nearest-neighbour covariant Laplacian.
The cost is the one-link ball and is independent of the generated scale. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_fixedOutputWeighted
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (background : PhysicalGaugeBackground d N Nc)
    {spacing rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 ≤ rate) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (ι := ActiveGaugeRegion.Site Omega)
      (κ := ActiveGaugeRegion.Site Omega)
      (g := SUNLieCoord Nc)
      (cmp99ActiveRegionSourceCovariantLaplacian
        Omega rho background spacing)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
        d spacing rate) rate := by
  let L := cmp99ActiveRegionSourceCovariantLaplacian
    Omega rho background spacing
  let beta : ℝ := 4 * d / spacing ^ 2
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    positivity
  have hfinite : FinitePiLpTypedFiniteRange L
      (fun target source => finBoxDist target.1 source.1) 1 := by
    exact cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
      Omega rho background spacing
  have hbound : FinitePiLpTypedKernelBound L (fun _ _ => beta) := by
    apply finitePiLpKernelBound_of_opNorm_le
    exact norm_cmp99ActiveRegionSourceCovariantLaplacian_le
      Omega rho background hspacing
  have hcard : ∀ target : ActiveGaugeRegion.Site Omega,
      (Finset.univ.filter (fun source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1 ≤ 1)).card ≤ 3 ^ d := by
    intro target
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_ball_card_le Omega target 1
  simpa [L, beta,
    cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude] using
      finitePiLpTypedFixedOutputWeightedKernelBound_of_finiteRange L
        (fun target source => finBoxDist target.1 source.1)
        1 (3 ^ d) hbeta hrate hfinite hbound hcard

/-- The complete generated physical precision in the exact fixed-output
orientation of CMP99 (3.88).  The displayed amplitude is the literal sum of
the Laplacian budget and the normalized mass budget. -/
theorem cmp99SourceGeneratedPhysicalPrecision_directFixedOutputWeighted
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpTypedFixedOutputWeightedKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (κ := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        background budget fineSmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude
        d M depth spacing epsilon rate) rate := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let L := cmp99ActiveRegionSourceCovariantLaplacian
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing
  let Qmass := T.Qprime.adjoint.comp T.Qprime
  let mass := cmp99SourceGeneratedPhysicalMass
    d M (depth + 1) spacing epsilon
  have hL : FinitePiLpTypedFixedOutputWeightedKernelBound L
      (fun target source => finBoxDist target.1 source.1)
      (cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
        d spacing rate) rate := by
    exact cmp99ActiveRegionSourceCovariantLaplacian_fixedOutputWeighted
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc) background hspacing hrate
  have hQ : FinitePiLpTypedFixedOutputWeightedKernelBound Qmass
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ (depth + 1)) rate := by
    simpa [regions, T, Qmass] using
      cmp99SourceIteratedLift_QprimeMass_fixedOutputWeighted
        Omega (depth + 1) hd hM (matrixSUNAdjointModel Nc)
        spacing epsilon rate hrate background budget.toRadiusChain fineSmall
  have hmass : FinitePiLpTypedFixedOutputWeightedKernelBound (mass • Qmass)
      (fun target source => finBoxDist target.1 source.1)
      (|mass| *
        (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
          (cmp99SourceBlockAverageWeight M d) ^ (depth + 1))) rate :=
    finitePiLpTypedFixedOutputWeightedKernelBound_smul mass hQ
  have hsum := finitePiLpTypedFixedOutputWeightedKernelBound_add hL hmass
  rw [cmp99SourceGeneratedPhysicalPrecision, cmp99SourceGaugePrecision]
  simpa [regions, T, L, Qmass, mass,
    cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude] using hsum

end

end YangMills.RG
