/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389GeneratedMassGreenInsertion
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
# PRE-VALIDATION: ambient generated-mass insertion in CMP99 (3.89)

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

This file transports the literal generated counting mass from its active
carrier to the separated ambient carrier and then installs the printed scalar
mass `cmp99SourceGeneratedPhysicalMass`.  The two normalizations remain
separate in the endpoint: one surviving block-average weight comes from
`Q'^* Q'`, while the physical mass is an explicit absolute-value factor.

No cell sum, complete third species, full CMP99 (3.89), or contraction is
claimed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The literal generated counting mass, transported to the separated
ambient carrier by the already fixed full-site equivalence. -/
noncomputable def cmp99SourceSeparatedGeneratedCountingMass
    (hL : 2 ≤ L) (depth : ℕ) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := L)
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  finitePiLpTypedKernelReindex e e
    (regions.generatedCountingMass (by norm_num) hL rho spacing epsilon
      background chain fineSmall)

/-- Reindexing the varying Green/cutoff insertion to the separated ambient
carrier loses neither the common metric nor another cardinality factor. -/
theorem cmp99SourceSeparatedGeneratedCountingMass_GreenCutoffValue_le
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (rho : SUNAdjointModel Nc) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing A c hc
      hAcoer B0 delta0 ell)
    (target probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) :
    (∑ source : FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)),
      ‖cmp99SourceSeparatedGeneratedCountingMass
          (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon
          background chain fineSmall
        (singleFinitePiLp source
          (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
            hAcoer
            ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
              L K Q depth).symm target)
            probe v
            ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
              L K Q depth).symm source))) target‖) ≤
      (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
        (((8 * P.derivBound) / (K : ℝ)) *
          ((B0 * ell ^ 2) * Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist
              (cmp99SourceSeparatedLargeBlockSide L K depth) Q
              target probe : ℝ))) * ‖v‖)) := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := L)
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) (depth + 1)
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let T : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) →L[ℝ]
    ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) :=
    regions.generatedCountingMass (by norm_num) hL rho spacing epsilon
      background chain fineSmall
  let phi : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieCoord Nc := fun source =>
    cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc hAcoer
      (e.symm target) probe v (e.symm source)
  calc
    (∑ source, ‖cmp99SourceSeparatedGeneratedCountingMass
        (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon
        background chain fineSmall
      (singleFinitePiLp source
        (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
          hAcoer (e.symm target) probe v (e.symm source))) target‖) =
      ∑ source, ‖T
        (singleFinitePiLp source
          (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
            hAcoer (e.symm target) probe v source)) (e.symm target)‖ := by
        simpa only [cmp99SourceSeparatedGeneratedCountingMass, regions, T,
          phi, e, Equiv.symm_apply_apply] using
          (sum_norm_finitePiLpTypedKernelReindex_single_varying
            e e T phi target)
    _ ≤ (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
        (((8 * P.derivBound) / (K : ℝ)) *
          ((B0 * ell ^ 2) * Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist
              (cmp99SourceSeparatedLargeBlockSide L K depth) Q
              target probe : ℝ))) * ‖v‖)) := by
      simpa only [e, T, Equiv.apply_symm_apply] using
        (cmp99Eq389GeneratedCountingMass_GreenCutoffValue_le
          (L := L) (K := K) (Q := Q) P hL depth rho spacing epsilon
          background chain fineSmall cell Omega U A c hc hAcoer B0 delta0
          ell C (e.symm target) probe v)

/-- Literal separated-ambient third-species summand, with the physical scalar
mass kept outside the normalized generated counting mass. -/
noncomputable def cmp99Eq389GeneratedMassAmbientCorrection
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (rho : SUNAdjointModel Nc) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (target probe source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) : SUNLieCoord Nc :=
  cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) spacing epsilon •
    cmp99SourceSeparatedGeneratedCountingMass
      (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon background
      chain fineSmall
      (singleFinitePiLp source
        (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
          hAcoer
          ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth).symm target)
          probe v
          ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth).symm source))) target

/-- Installing the literal physical scalar mass multiplies the already
normalized ambient estimate by exactly its absolute value. -/
theorem cmp99Eq389GeneratedMassAmbientCorrection_sum_norm_le
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (rho : SUNAdjointModel Nc) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ edge : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background edge : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing A c hc
      hAcoer B0 delta0 ell)
    (target probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) :
    (∑ source, ‖cmp99Eq389GeneratedMassAmbientCorrection
      (L := L) (K := K) (Q := Q) P hL depth rho spacing epsilon background
      chain fineSmall cell Omega A c hc hAcoer target probe source v‖) ≤
      |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1)
          spacing epsilon| *
        ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
          (((8 * P.derivBound) / (K : ℝ)) *
            ((B0 * ell ^ 2) * Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                target probe : ℝ))) * ‖v‖))) := by
  calc
    (∑ source, ‖cmp99Eq389GeneratedMassAmbientCorrection
      (L := L) (K := K) (Q := Q) P hL depth rho spacing epsilon background
      chain fineSmall cell Omega A c hc hAcoer target probe source v‖) =
      |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1) spacing epsilon| *
        ∑ source, ‖cmp99SourceSeparatedGeneratedCountingMass
          (L := L) (K := K) (Q := Q) hL depth rho spacing epsilon background
          chain fineSmall
          (singleFinitePiLp source
            (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c
              hc hAcoer
              ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
                L K Q depth).symm target)
              probe v
              ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
                L K Q depth).symm source))) target‖ := by
        simp only [cmp99Eq389GeneratedMassAmbientCorrection, norm_smul,
          Real.norm_eq_abs, Finset.mul_sum]
    _ ≤ |cmp99SourceGeneratedPhysicalMass 4 L (depth + 1)
          spacing epsilon| *
        ((cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
          (((8 * P.derivBound) / (K : ℝ)) *
            ((B0 * ell ^ 2) * Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                target probe : ℝ))) * ‖v‖))) := by
      exact mul_le_mul_of_nonneg_left
        (cmp99SourceSeparatedGeneratedCountingMass_GreenCutoffValue_le
          (L := L) (K := K) (Q := Q) P hL depth rho spacing epsilon
          background chain fineSmall cell Omega U A c hc hAcoer B0 delta0
          ell C target probe v)
        (abs_nonneg _)

end

end YangMills.RG
