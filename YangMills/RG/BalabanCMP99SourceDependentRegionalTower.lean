/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceDependentOmegaGeometry
import YangMills.RG.BalabanCMP99SourceUbarRadiusBudget
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalTower

/-!
# A retained physical tower on one dependent CMP99 source domain

CMP96 permits more than one admissible nested `Omega` sequence, so that
sequence is physical boundary data.  Once it is fixed, however, the operator
regions at every averaging resolution are canonical: the scale-`k` operator
domain is the complete-block lift of the printed physical domain.

This file performs that last composition.  It proves block saturation and
exact coarsening at every positive resolution, then generates all retained
prefixes from one fine background and the literal recursive `Ubar` map.  No
operator region, coarse background, scale carrier, or scale isometry is a
caller input.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe v

variable {Q M Nc j depth : ℕ}
variable [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- The coarse active region belonging to the literal physical member
`Omega_r`, after proving the p. 408 `tilde Pi^5` envelope. -/
def operatorCoarseRegion
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) : ActiveGaugeRegion 4 (2 * Q) :=
  cmp99OmegaCoarseActiveGaugeRegion (D.toLargeBlockGeometry hpi5) r

@[simp] theorem operatorCoarseRegion_sites
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) :
    (D.operatorCoarseRegion hpi5 r).sites = D.fineRegion r := rfl

/-- The canonical scale-`k` complete-block realization of `Omega_r`. -/
noncomputable def operatorRegion
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) (k : ℕ) :
    ActiveGaugeRegion 4 (cmp99RegionalLatticeSize M (2 * Q) k) :=
  cmp99IteratedLiftActiveRegion (M := M)
    (D.operatorCoarseRegion hpi5 r) k

@[simp] theorem operatorRegion_zero
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) :
    D.operatorRegion (M := M) hpi5 r 0 =
      D.operatorCoarseRegion hpi5 r := rfl

/-- Every positive-resolution realization is a union of complete averaging
blocks. -/
theorem operatorRegion_blockSaturated
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) (k : ℕ) :
    (D.operatorRegion (M := M) hpi5 r (k + 1)).BlockSaturated :=
  cmp99IteratedLiftActiveRegion_blockSaturated
    (D.operatorCoarseRegion hpi5 r) k

/-- Exact dependent transition: complete-block coarsening at level `k+1`
returns level `k`, with no transport by an unaudited equality. -/
theorem activeCoarseRegion_operatorRegion_succ_eq
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) (k : ℕ) :
    cmp99ActiveCoarseRegion (M := M)
        (N' := cmp99RegionalLatticeSize M (2 * Q) k)
        (D.operatorRegion (M := M) hpi5 r (k + 1)) =
      D.operatorRegion (M := M) hpi5 r k :=
  cmp99ActiveCoarseRegion_iteratedLift_succ_eq
    (D.operatorCoarseRegion hpi5 r) k

/-- The retained source tower on the selected physical domain.  Its regions,
coarse backgrounds and scale carriers are all generated internally. -/
noncomputable def retainedPhysicalTower
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) depth) (SUN Nc))
    (budget : CMP99SourceUbarScalarBudget 4 M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    CMP99SourceRetainedPhysicalTower rho
      (D.operatorRegion (M := M) hpi5 r depth)
      M spacing background depth :=
  cmp99SourceRetainedPhysicalTower (by norm_num) hM rho
    (D.operatorCoarseRegion hpi5 r) depth spacing epsilon background
    budget.toRadiusChain fineSmall

/-- Every retained prefix has the requested averaging order. -/
theorem retainedPhysicalTower_prefix_depth
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) depth) (SUN Nc))
    (budget : CMP99SourceUbarScalarBudget 4 M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (k : Fin (depth + 1)) :
    ((D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
      budget fineSmall).towerAt k).depth = k.val :=
  (D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
    budget fineSmall).towerAt_depth k

/-- Literal composition order for consecutive prefixes of the generated
regional tower. -/
theorem retainedPhysicalTower_Qprime_succ
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) depth) (SUN Nc))
    (budget : CMP99SourceUbarScalarBudget 4 M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (k : Fin depth) :
    let T := D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
      budget fineSmall
    (T.towerAt k.succ).Qprime =
      (T.nextAverage k).comp (T.towerAt k.castSucc).Qprime := by
  dsimp only
  exact CMP99SourceRetainedPhysicalTower.Qprime_succ _ k

/-- Exact `C_k` normalization for every physical retained prefix. -/
theorem retainedPhysicalTower_prefix_comp_weightedAdjoint
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) depth) (SUN Nc))
    (budget : CMP99SourceUbarScalarBudget 4 M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (k : Fin (depth + 1)) :
    let T := D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
      budget fineSmall
    (T.towerAt k).Qprime.comp (T.towerAt k).weightedAdjoint =
      ContinuousLinearMap.id ℝ (T.towerAt k).TerminalSpace.carrier := by
  dsimp only
  exact CMP99SourceRetainedPhysicalTower.prefix_comp_weightedAdjoint _ k

/-- Exact source-Hilbert norm law for the generated prefix adjoint. -/
theorem retainedPhysicalTower_weightedAdjoint_norm
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) depth) (SUN Nc))
    (budget : CMP99SourceUbarScalarBudget 4 M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (k : Fin (depth + 1))
    (eta : ((D.retainedPhysicalTower hpi5 r hM rho spacing epsilon
      background budget fineSmall).towerAt k).TerminalSpace.carrier) :
    let T := D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
      budget fineSmall
    cmp99SourceSpacingNorm 4 spacing ((T.towerAt k).weightedAdjoint eta) =
      Real.sqrt (cmp99SourceTowerNormalization k.val) *
        cmp99SourceSpacingNorm 4 (T.towerAt k).terminalSpacing eta := by
  dsimp only
  have h := (D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
    budget fineSmall).towerAt k |>.weightedAdjoint_norm_eq_sqrt_Cj eta
  simpa [(D.retainedPhysicalTower hpi5 r hM rho spacing epsilon background
    budget fineSmall).towerAt_depth k] using h

/-- In the printed spacing-weighted Hilbert convention every scale factor is
one, hence `C_k = product_{i<k} 1 = 1` and is strictly positive. -/
theorem retainedPhysicalTower_normalization_eq_one_pos
    (k : ℕ) :
    cmp99SourceTowerNormalization k = 1 ∧
      0 < cmp99SourceTowerNormalization k := by
  exact ⟨cmp99SourceTowerNormalization_eq_one k,
    cmp99SourceTowerNormalization_pos k⟩

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
