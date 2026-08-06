/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389GeneratedMassCommonMetric
import YangMills.RG.BalabanCMP99Eq389SignedCutoffLaplacianPhysicalBound
import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange

/-!
# PRE-VALIDATION: Green insertion for the generated third species

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these results have not yet been verified by the compiler.

This file inserts the literal regional Green value and signed-cutoff
difference into the varying-value generated counting-mass estimate.  The
terminal fibre has diameter `L^(depth+1)-1`, while the source-faithful signed
cutoff has scale `2*K*L^(depth+1)`.  Their product leaves the explicit cost
`8*derivBound/K` before any cell or layer sum.

No separated-ambient mass reindexing, physical scalar mass, cell sum,
complete third species, full CMP99 (3.89), or contraction is claimed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389GreenInsertionSeparatedBlockSide
    (L K depth : ℕ) [NeZero L] [NeZero K] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth) :=
  ⟨by
    unfold cmp99SourceSeparatedLargeBlockSide
    exact (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1))).ne'⟩

private instance instNeZeroEq389GreenInsertionAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K)
      (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Across one generated terminal fibre, the literal signed cutoff difference
costs exactly the source-visible budget `8*derivBound/K`. -/
theorem norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_le_of_sameTerminalBlock
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target) :
    ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth source) -
        cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth target)‖ ≤
      (8 * P.derivBound) / (K : ℝ) := by
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  have hdist : finBoxDist (e target) (e source) =
      finBoxDist target.1 source.1 := by
    have h :=
      finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
        L K Q depth (e target) (e source)
    simpa only [e, Equiv.symm_apply_apply] using h.symm
  have hdiam : finBoxDist target.1 source.1 ≤ L ^ (depth + 1) - 1 :=
    cmp99SourceIteratedLift_terminalBlock_diameter
      (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1) source target hsame
  have hdistNat : finBoxDist (e target) (e source) ≤ L ^ (depth + 1) := by
    rw [hdist]
    exact hdiam.trans (Nat.sub_le _ _)
  have hdistReal :
      (finBoxDist (e target) (e source) : ℝ) ≤
        (L ^ (depth + 1) : ℝ) := by
    exact_mod_cast hdistNat
  have hslope :=
    norm_cmp99SourceSeparatedSignedLargeBlockSquarePartition_value_sub_le
      (L := L) (K := K) (Q := Q) (depth := depth)
      P cell (e target) (e source)
  have hslopeNonneg : 0 ≤
      (16 * P.derivBound) /
        cmp99SourceSeparatedLargeBlockCutoffScale L K depth :=
    div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (Nat.cast_nonneg _)
  calc
    ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (e source) -
        cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (e target)‖ ≤
        ((16 * P.derivBound) /
          cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
          (finBoxDist (e target) (e source) : ℝ) := hslope
    _ ≤ ((16 * P.derivBound) /
          cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
          (L ^ (depth + 1) : ℝ) :=
      mul_le_mul_of_nonneg_left hdistReal hslopeNonneg
    _ = (8 * P.derivBound) / (K : ℝ) :=
      cmp99SourceSeparatedSignedLargeBlockSlope_mul_precisionRange
        P L K depth

/-- The literal extended regional Green has one common CMP99 (3.42) metric
at every point of a generated terminal fibre. -/
theorem norm_cmp99RegionalExtendedDirichletGreen_single_apply_le_commonMetric
    (depth : ℕ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (spacing : ℝ)
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
    (v : SUNLieCoord Nc) :
    ‖cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
        (singleFinitePiLp probe v)
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source)‖ ≤
      (B0 * ell ^ 2) * Real.exp (-(delta0 *
        (cmp99Eq342RescaledBlockDist
          (cmp99SourceSeparatedLargeBlockSide L K depth) Q
          (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth target) probe : ℝ))) * ‖v‖ := by
  have hvalue :=
    (C.extended_value_bound Omega rho U spacing A c hc hAcoer
      B0 delta0 ell).2.2 probe
      (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
        L K Q depth source) v
  rw [cmp99Eq342RescaledBlockDist_sourceSeparated_eq_of_sameTerminalBlock
    (L := L) (K := K) (Q := Q) depth source target probe hsame] at hvalue
  exact hvalue

/-- Literal varying value inserted between the generated mass and the source
cutoff in the third species of CMP99 (3.88). -/
noncomputable def cmp99Eq389GeneratedMassGreenCutoffValue
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
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
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1))) : SUNLieCoord Nc :=
  (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth source) -
      cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
        (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth target)) •
    cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
      (singleFinitePiLp probe v)
      (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
        L K Q depth source)

/-- On the actual terminal fibre, the inserted Green/cutoff value has the
common metric and the explicit inverse-`K` cutoff cost. -/
theorem norm_cmp99Eq389GeneratedMassGreenCutoffValue_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (spacing : ℝ)
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
    (target source : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hsame : (cmp99SourceIteratedLiftActiveRegionChain (M := L)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
      (depth + 1)).SameTerminalBlock source target) :
    ‖cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
        hAcoer target probe v source‖ ≤
      ((8 * P.derivBound) / (K : ℝ)) *
        ((B0 * ell ^ 2) * Real.exp (-(delta0 *
          (cmp99Eq342RescaledBlockDist
            (cmp99SourceSeparatedLargeBlockSide L K depth) Q
            (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
              L K Q depth target) probe : ℝ))) * ‖v‖) := by
  rw [cmp99Eq389GeneratedMassGreenCutoffValue, norm_smul,
    Real.norm_eq_abs]
  exact mul_le_mul
    (norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_le_of_sameTerminalBlock
      (L := L) (K := K) (Q := Q) P depth cell source target hsame)
    (norm_cmp99RegionalExtendedDirichletGreen_single_apply_le_commonMetric
      (L := L) (K := K) (Q := Q) depth source target probe hsame
      Omega rho U spacing A c hc hAcoer B0 delta0 ell C v)
    (norm_nonneg _)
    (div_nonneg (mul_nonneg (by norm_num) P.derivBound_nonneg)
      (Nat.cast_nonneg _))

/-- The generated counting mass consumes the literal inserted Green/cutoff
value with the exact one surviving normalized block weight. -/
theorem cmp99Eq389GeneratedCountingMass_GreenCutoffValue_le
    (P : CMP95SourceSmoothPartitionProfile) (hL : 2 ≤ L) (depth : ℕ)
    (rho : SUNAdjointModel Nc) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
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
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)))
    (probe : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc) :
    (∑ source,
        ‖(cmp99SourceIteratedLiftActiveRegionChain (M := L)
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1)).generatedCountingMass (by norm_num) hL rho
          spacing epsilon background chain fineSmall
          (singleFinitePiLp source
            (cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c
              hc hAcoer target probe v source)) target‖) ≤
      (cmp99SourceBlockAverageWeight L 4) ^ (depth + 1) *
        (((8 * P.derivBound) / (K : ℝ)) *
          ((B0 * ell ^ 2) * Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist
              (cmp99SourceSeparatedLargeBlockSide L K depth) Q
              (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
                L K Q depth target) probe : ℝ))) * ‖v‖)) := by
  let phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := L)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
        (depth + 1)) (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun source =>
      cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c hc
        hAcoer target probe v source
  change (∑ source,
      ‖(cmp99SourceIteratedLiftActiveRegionChain (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1)).generatedCountingMass (by norm_num) hL rho
        spacing epsilon background chain fineSmall
        (singleFinitePiLp source (phi source)) target‖) ≤ _
  apply cmp99SourceIteratedLift_sum_norm_generatedCountingMass_varying_le
    (Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
    (depth := depth + 1) (by norm_num) hL rho spacing epsilon background
    chain fineSmall target phi
  · positivity
  · intro source hsame
    change ‖cmp99Eq389GeneratedMassGreenCutoffValue P depth cell Omega A c
      hc hAcoer target probe v source‖ ≤ _
    exact norm_cmp99Eq389GeneratedMassGreenCutoffValue_le
      (L := L) (K := K) (Q := Q) P depth cell Omega rho U spacing A c hc
      hAcoer B0 delta0 ell C target source probe v hsame

end

end YangMills.RG
