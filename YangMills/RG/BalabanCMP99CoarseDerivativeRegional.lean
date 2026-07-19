/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CoarseDerivativeRemainder
import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare

/-!
# Regional CMP99 coarse-derivative control

The recursive source tower acts on active regions, whereas the exact
coarse-transport decomposition is most naturally proved on the full
periodic box.  Block saturation identifies the full average of a zero
extension with the zero extension of the literal regional average.  This
module consumes that identity and transports the physical `Ubar` gradient
bound to the exact regional operator used by the tower.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal full source average contracts counting-space `L²` by the
exact block weight `M⁻ᵈ`.  Parallel transport costs nothing because the
adjoint action is isometric. -/
theorem norm_cmp99FullSourceBlockAverage_sq_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 := by
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  have hblock (y : FinBox d N') :
      ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2 ≤
        cmp99SourceBlockAverageWeight M d *
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
            ‖phi x.1‖ ^ 2 := by
    let I := {x : FinBox d (M * N') // x ∈ blockOf M N' y}
    let v : I → SUNLieCoord Nc := fun x =>
      rho.adCLM
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
        (phi x.1)
    have hnorm : cmp99SourceBlockAverageWeight M d *
        (Fintype.card I : ℝ) = 1 := by
      change cmp99SourceBlockAverageWeight M d *
        (Fintype.card {x : FinBox d (M * N') // x ∈ blockOf M N' y} : ℝ) = 1
      rw [Fintype.card_coe, blockOf_card, Nat.cast_pow]
      exact cmp99SourceBlockAverageWeight_mul_card
    have hmean := norm_normalized_fintype_sum_sq_le
      (cmp99SourceBlockAverageWeight M d) hw hnorm v
    change ‖cmp99SourceBlockAverageWeight M d • ∑ x : I, v x‖ ^ 2 ≤ _
    calc
      _ ≤ cmp99SourceBlockAverageWeight M d * ∑ x : I, ‖v x‖ ^ 2 := hmean
      _ = cmp99SourceBlockAverageWeight M d *
          ∑ x : I, ‖phi x.1‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _hx
        exact congrArg (fun z : ℝ => z ^ 2) (rho.norm_ad _ _)
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ y : FinBox d N', ‖cmp99FullSourceBlockAverage rho U phi y‖ ^ 2) ≤
      ∑ y : FinBox d N', cmp99SourceBlockAverageWeight M d *
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
          ‖phi x.1‖ ^ 2 := by
      gcongr with y _
      simpa only [cmp99FullSourceBlockAverage_apply] using hblock y
    _ = cmp99SourceBlockAverageWeight M d *
        ∑ x : FinBox d (M * N'), ‖phi x‖ ^ 2 := by
      rw [← Finset.mul_sum, ← sum_blockOf M N']
      congr 1
      apply Finset.sum_congr rfl
      intro y _hy
      exact (Finset.sum_subtype (blockOf M N' y) (fun _ => Iff.rfl)
        (fun x => ‖phi x‖ ^ 2)).symm

/-- Regional source average contraction, obtained by the exact zero-extension
dictionary rather than by an unrelated operator-norm estimate. -/
theorem norm_cmp99SourceRegionalAverage_sq_le
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) phi‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * ‖phi‖ ^ 2 := by
  have hfull := norm_cmp99FullSourceBlockAverage_sq_le rho U
    (extendZeroZeroCLM Omega phi)
  rw [cmp99FullSourceBlockAverage_extendZero_eq Omega hOmega rho U phi] at hfull
  rw [norm_extendZeroZeroCLM_eq, norm_extendZeroZeroCLM_eq] at hfull
  exact hfull

/-- Regional physical one-step gradient bound.  Both derivatives are the
literal full-periodic covariant derivatives of the corresponding Dirichlet
zero extensions, so boundary bonds are retained exactly. -/
theorem norm_covariantD0_cmp99SourceRegionalAverage_physicalUbar_sq_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    let data := cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
      weight epsilonFine epsilonFine_nonneg noWinding fine_small
    let coarseOmega :=
      cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    let coarsePhi := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc)
        background) phi
    ‖covariantD0CLM (matrixSUNAdjointModel Nc) data.nextBackground
        (extendZeroZeroCLM coarseOmega coarsePhi)‖ ^ 2 ≤
      2 * (((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2) *
          ‖covariantD0CLM (matrixSUNAdjointModel Nc) background
            (extendZeroZeroCLM Omega phi)‖ ^ 2 +
        2 * (cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            cmp99SourceUbarNextFineRadius d M epsilonFine)) ^ 2 *
            (d : ℝ)) * ‖phi‖ ^ 2 := by
  dsimp only
  have hfull :=
    norm_covariantD0_cmp99FullSourceBlockAverage_physicalUbar_sq_le
      hd hM Omega background weight epsilonFine epsilonFine_nonneg
      noWinding logSmall fine_small (extendZeroZeroCLM Omega phi)
  rw [cmp99FullSourceBlockAverage_extendZero_eq
    Omega hOmega (matrixSUNAdjointModel Nc) background phi] at hfull
  rw [norm_extendZeroZeroCLM_eq Omega phi] at hfull
  exact hfull

end

end YangMills.RG
