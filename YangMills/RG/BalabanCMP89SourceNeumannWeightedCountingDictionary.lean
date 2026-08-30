import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision

/-!
# CMP89 Neumann source-weighted/counting dictionary

Compiler-verified in a fresh Colab checkout at source checkpoint
`a1fe7d151400d99fe0d89e5d430ddb992a6168b8`.

CMP89 (1.3) uses the same `spacing^d` factor in the site and internal-bond
pairings. Consequently the counting-Hilbert adjoint used by the literal
Neumann Laplacian is also the adjoint for the printed pairings. The retained
`Qprime` term has different fine and terminal spacings; its exact volume
ratio is the already sealed CMP85 weighted/counting coefficient dictionary.

This module composes those two facts without identifying the printed
coefficient with the counting coefficient.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

/-- Multiplying both Hilbert pairings by the same scalar leaves the adjoint
identity unchanged. -/
theorem cmp89SourceCommonSpacingWeight_adjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : E →L[ℝ] F) (d : ℕ) (spacing : ℝ) (phi : E) (psi : F) :
    spacing ^ d * inner ℝ phi (D.adjoint psi) =
      spacing ^ d * inner ℝ (D phi) psi := by
  rw [ContinuousLinearMap.adjoint_inner_right]

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Exact printed common-weight quadratic form of the internal-bond Neumann
Laplacian. -/
theorem cmp99SourceSpacingPairing_neumannRegionalLaplacian
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99SourceSpacingPairing d spacing phi
        (cmp89SourceNeumannRegionalLaplacian Omega rho U spacing phi) =
      spacing ^ d *
        ‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 := by
  rw [cmp99SourceSpacingPairing,
    inner_cmp89SourceNeumannRegionalLaplacian]

variable {M depth : ℕ} [NeZero M]
variable {Omega : ActiveGaugeRegion d N}
variable {rho : SUNAdjointModel Nc} {spacing : ℝ}
variable {background : GaugeConfig d N (SUN Nc)}

/-- The counting coefficient times the fine volume element is exactly the
printed weighted coefficient times the terminal volume element. -/
theorem cmp85SourcePrefixCountingCoefficient_mul_fineVolume
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (a : ℝ) (hspacing : 0 < spacing)
    (r : CMP85PositivePrefix depth) :
    spacing ^ d * cmp85SourcePrefixCountingCoefficient T a r =
      cmp85SourcePrefixWeightedCoefficient T a r *
        (T.towerAt r.1).terminalSpacing ^ d := by
  unfold cmp85SourcePrefixCountingCoefficient
  unfold cmp85SourcePrefixVolumeRatio
  field_simp [pow_ne_zero d hspacing.ne']

/-- Exact source-weighted quadratic form of the retained three-term Neumann
precision. The Neumann energy and bare mass use the fine volume element;
the `Qprime` term uses the printed terminal volume element and weighted
coefficient. -/
theorem cmp99SourceSpacingPairing_retainedNeumannPrefixGaugePrecision
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (r : CMP85PositivePrefix depth)
    (mass a : ℝ) (hspacing : 0 < spacing)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99SourceSpacingPairing d spacing phi
        (cmp89SourceRetainedNeumannPrefixGaugePrecision
          T r mass a phi) =
      spacing ^ d *
          (‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho background spacing phi‖ ^ 2 +
            mass ^ 2 * ‖phi‖ ^ 2) +
        cmp85SourcePrefixWeightedCoefficient T a r *
          (T.towerAt r.1).terminalSpacing ^ d *
            ‖(T.towerAt r.1).Qprime phi‖ ^ 2 := by
  rw [cmp99SourceSpacingPairing,
    inner_cmp89SourceRetainedNeumannPrefixGaugePrecision]
  have hcoeff := cmp85SourcePrefixCountingCoefficient_mul_fineVolume
    T a hspacing r
  calc
    spacing ^ d *
        (‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho background spacing phi‖ ^ 2 +
          mass ^ 2 * ‖phi‖ ^ 2 +
          cmp85SourcePrefixCountingCoefficient T a r *
            ‖(T.towerAt r.1).Qprime phi‖ ^ 2) =
      spacing ^ d *
          (‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho background spacing phi‖ ^ 2 +
            mass ^ 2 * ‖phi‖ ^ 2) +
        (spacing ^ d * cmp85SourcePrefixCountingCoefficient T a r) *
          ‖(T.towerAt r.1).Qprime phi‖ ^ 2 := by ring
    _ = _ := by rw [hcoeff]

end

end YangMills.RG
