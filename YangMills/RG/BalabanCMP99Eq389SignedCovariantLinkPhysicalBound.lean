/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389CovariantLinkCommonMetric
import YangMills.RG.BalabanCMP99Eq389SignedCutoffLaplacianPhysicalBound
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalCutoffIdentity

/-!
# PRE-VALIDATION: signed first species in CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module reinstantiates the first covariant-link species with the
source-faithful signed cutoff.  The signed endpoint pays the visible factor
two of the periodic boundary overlap: before the cell sum its source budget
contains the literal `8 * derivBound / K`.  A contractive right signed cutoff
then exposes the already sealed geometric overlap `16`.

The first-species operator is reconstructed from the exact ambient product
rule.  No abstract row/column symmetry, Combes--Thomas/Schur majorant,
Poincare constant or shared three-species constant is introduced here.
This is not the complete CMP99 (3.89) estimate and does not attain window 15.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SignedCovariantAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- One-step slope budget of the signed source-separated cutoff. -/
noncomputable def cmp99Eq389SignedCovariantLinkSlopeBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) : ℝ :=
  (16 * P.derivBound) /
    cmp99SourceSeparatedLargeBlockCutoffScale L K depth

theorem cmp99Eq389SignedCovariantLinkSlopeBudget_nonneg
    (P : CMP95SourceSmoothPartitionProfile)
    (L K depth : ℕ) :
    0 ≤ cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth := by
  unfold cmp99Eq389SignedCovariantLinkSlopeBudget
  exact div_nonneg
    (mul_nonneg (by norm_num) P.derivBound_nonneg) (Nat.cast_nonneg _)

/-- A positive incident edge pays the literal signed cutoff slope. -/
theorem norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shift_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x -
        cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (x.shift i)‖ ≤
      cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth := by
  let A := cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth
  have hA : 0 ≤ A :=
    cmp99Eq389SignedCovariantLinkSlopeBudget_nonneg P L K depth
  have h :=
    norm_cmp99SourceSeparatedSignedLargeBlockSquarePartition_value_sub_le
      (L := L) (K := K) (Q := Q) (depth := depth)
      P cell x (x.shift i)
  change ‖_ - _‖ ≤ A
  calc
    ‖_ - _‖ =
        ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
            (x.shift i) -
          cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x‖ :=
      norm_sub_rev _ _
    _ ≤ A * (finBoxDist x (x.shift i) : ℝ) := h
    _ ≤ A * 1 := by
      gcongr
      exact_mod_cast finBoxDist_shift_le x i
    _ = A := mul_one A

/-- A negative incident edge pays the same signed cutoff slope. -/
theorem norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shiftBack_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x -
        cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
          (x.shiftBack i)‖ ≤
      cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth := by
  let A := cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth
  have hA : 0 ≤ A :=
    cmp99Eq389SignedCovariantLinkSlopeBudget_nonneg P L K depth
  have h :=
    norm_cmp99SourceSeparatedSignedLargeBlockSquarePartition_value_sub_le
      (L := L) (K := K) (Q := Q) (depth := depth)
      P cell x (x.shiftBack i)
  change ‖_ - _‖ ≤ A
  calc
    ‖_ - _‖ =
        ‖cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
            (x.shiftBack i) -
          cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x‖ :=
      norm_sub_rev _ _
    _ ≤ A * (finBoxDist x (x.shiftBack i) : ℝ) := h
    _ ≤ A * 1 := by
      gcongr
      exact_mod_cast finBoxDist_shiftBack_le x i
    _ = A := mul_one A

/-- Explicit pre-overlap amplitude of the signed first species.  The first
`4` counts directions; the inner `8` is the source-faithful signed
slope-times-generated-derivative-scale constant. -/
noncomputable def cmp99Eq389SignedCovariantLinkSourceBudget
    (P : CMP95SourceSmoothPartitionProfile)
    (B0 delta0 : ℝ) (K : ℕ) : ℝ :=
  4 * ((8 * B0 * P.derivBound) / (K : ℝ)) *
    (1 + Real.exp delta0)

/-- The literal signed cutoff and one canonical regional Green obey the
complete pointwise first-species estimate before the right cutoff and cell
sum. -/
theorem
    norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_signedSeparated_le
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ))
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    ‖cmp99CovariantCutoffLinkDerivative rho U 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell)
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (singleFinitePiLp source v))) x‖ ≤
      cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K *
        Real.exp (-(delta0 *
          (cmp99Eq342RescaledBlockDist
            (cmp99SourceSeparatedLargeBlockSide L K depth) Q
            x source.1 : ℝ))) * ‖v‖ := by
  let slope := cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth
  have hslope : 0 ≤ slope :=
    cmp99Eq389SignedCovariantLinkSlopeBudget_nonneg P L K depth
  have hmain :=
    norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_commonMetric
      Omega rho U A c hc hAcoer B0 delta0 (L ^ (depth + 1) : ℝ) C
      (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell)
      source v x slope hslope
      (norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shift_le
        (L := L) (K := K) (Q := Q) P depth cell x)
      (norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shiftBack_le
        (L := L) (K := K) (Q := Q) P depth cell x)
  calc
    ‖cmp99CovariantCutoffLinkDerivative rho U 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell)
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (singleFinitePiLp source v))) x‖ ≤
        slope * ∑ _i : Fin 4,
          ((B0 * (L ^ (depth + 1) : ℝ)) *
                Real.exp (-(delta0 *
                  (cmp99Eq342RescaledBlockDist
                    (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                    x source.1 : ℝ))) * ‖v‖ +
            (B0 * (L ^ (depth + 1) : ℝ)) *
                (Real.exp delta0 * Real.exp (-(delta0 *
                  (cmp99Eq342RescaledBlockDist
                    (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                    x source.1 : ℝ)))) * ‖v‖) := hmain
    _ = cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K *
        Real.exp (-(delta0 *
          (cmp99Eq342RescaledBlockDist
            (cmp99SourceSeparatedLargeBlockSide L K depth) Q
            x source.1 : ℝ))) * ‖v‖ := by
      have hscale :
          cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth *
              (B0 * (L ^ (depth + 1) : ℝ)) =
            (8 * B0 * P.derivBound) / (K : ℝ) := by
        unfold cmp99Eq389SignedCovariantLinkSlopeBudget
        calc
          ((16 * P.derivBound) /
                cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
              (B0 * (L ^ (depth + 1) : ℝ)) =
            B0 * (((16 * P.derivBound) /
                cmp99SourceSeparatedLargeBlockCutoffScale L K depth) *
              (L ^ (depth + 1) : ℝ)) := by ring
          _ = B0 * ((8 * P.derivBound) / (K : ℝ)) := by
            rw [cmp99SourceSeparatedSignedLargeBlockSlope_mul_precisionRange]
          _ = (8 * B0 * P.derivBound) / (K : ℝ) := by ring
      rw [Fin.sum_univ_four]
      unfold cmp99Eq389SignedCovariantLinkSourceBudget slope
      calc
        _ = 4 *
            (cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth *
              (B0 * (L ^ (depth + 1) : ℝ))) *
            (1 + Real.exp delta0) *
            Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                x source.1 : ℝ))) * ‖v‖ := by ring
        _ = 4 * ((8 * B0 * P.derivBound) / (K : ℝ)) *
            (1 + Real.exp delta0) *
            Real.exp (-(delta0 *
              (cmp99Eq342RescaledBlockDist
                (cmp99SourceSeparatedLargeBlockSide L K depth) Q
                x source.1 : ℝ))) * ‖v‖ := by
          rw [hscale]

/-- Ambient continuous linear operator whose pointwise value is the literal
first species.  It is reconstructed from the exact product rule as the
covariant-Laplacian commutator plus the separately named scalar correction. -/
noncomputable def cmp99Eq389SignedCovariantLinkAmbientOperator
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  let h : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
  let laplacian : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U 1
  let commutator : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
    finitePiLpScalarCommutator
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc) h laplacian
  let scalarCorrection : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
    finitePiLpScalarMultiplier
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (cmp99SourceSeparatedSignedCutoffLaplacianCoefficient
        (L := L) (K := K) P depth cell)
  commutator + scalarCorrection

/-- The reconstructed ambient operator is pointwise the literal covariant
link-derivative species, with no analytic estimate used. -/
theorem cmp99Eq389SignedCovariantLinkAmbientOperator_apply
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99Eq389SignedCovariantLinkAmbientOperator
        (L := L) (K := K) (Q := Q) P depth cell rho U phi x =
      cmp99CovariantCutoffLinkDerivative rho U 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell) phi x := by
  rw [cmp99Eq389SignedCovariantLinkAmbientOperator,
    ContinuousLinearMap.add_apply, finitePiLpScalarCommutator_apply_eq,
    finitePiLpScalarMultiplier_apply,
    cmp99GeneratedAmbientScaledCovariantLaplacian_scalarMultiplier,
    cmp99CutoffLaplacianCorrection_one_eq_sourceSeparatedSignedCoefficient]
  module

/-- The first-species ambient operator followed by one canonical regional
Dirichlet Green, before the right cutoff. -/
noncomputable def cmp99Eq389SignedCovariantLinkAmbientCorrection
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  (cmp99Eq389SignedCovariantLinkAmbientOperator
      (L := L) (K := K) (Q := Q) P depth cell rho U).comp
    (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer)

/-- Before the right cutoff, the signed first species has the printed common
metric and its own explicit source budget. -/
theorem
    cmp99Eq389SignedCovariantLinkAmbientCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ)) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq389SignedCovariantLinkAmbientCorrection
        (L := L) (K := K) (Q := Q) P depth cell Omega rho U
        A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K)
      delta0 := by
  have hbudget :
      0 ≤ cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K := by
    unfold cmp99Eq389SignedCovariantLinkSourceBudget
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) C.B0_nonneg) P.derivBound_nonneg)
          (Nat.cast_nonneg K)))
      (add_nonneg zero_le_one (Real.exp_pos _).le)
  refine ⟨hbudget, C.delta0_pos, ?_⟩
  intro source target v
  by_cases hsource : source ∈ Omega.sites
  · let sourceOmega : ActiveGaugeRegion.Site Omega := ⟨source, hsource⟩
    have hrestrict :
        restrictZeroCLM Omega (singleFinitePiLp source v) =
          singleFinitePiLp sourceOmega v := by
      apply PiLp.ext
      intro x
      by_cases hx : x.1 = source
      · have heq : x = sourceOmega := Subtype.ext hx
        subst x
        simp [restrictZeroCLM, sourceOmega]
      · have hne : x ≠ sourceOmega := by
          intro heq
          exact hx (congrArg Subtype.val heq)
        simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
    change ‖cmp99Eq389SignedCovariantLinkAmbientOperator
        (L := L) (K := K) (Q := Q) P depth cell rho U
        (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
          (singleFinitePiLp source v)) target‖ ≤ _
    rw [cmp99Eq389SignedCovariantLinkAmbientOperator_apply]
    change ‖cmp99CovariantCutoffLinkDerivative rho U 1
        (cmp99SourceSeparatedSignedLargeBlockCutoff
          P L K Q depth cell)
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega A hc hAcoer
            (restrictZeroCLM Omega (singleFinitePiLp source v)))) target‖ ≤ _
    rw [hrestrict]
    simpa [sourceOmega] using
      (norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_signedSeparated_le
        (L := L) (K := K) (Q := Q) P depth cell Omega rho U
        A c hc hAcoer B0 delta0 C sourceOmega v target)
  · have hrestrict :
        restrictZeroCLM Omega (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖cmp99Eq389SignedCovariantLinkAmbientOperator
        (L := L) (K := K) (Q := Q) P depth cell rho U
        (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer
          (singleFinitePiLp source v)) target‖ ≤ _
    unfold cmp99RegionalExtendedDirichletGreen
    simp only [ContinuousLinearMap.comp_apply, hrestrict, map_zero,
      PiLp.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg hbudget (Real.exp_pos _).le)
      (norm_nonneg v)

/-- One complete signed first-species cell, with the same signed cutoff on
the source before the regional Green. -/
noncomputable def cmp99Eq389SignedCovariantLinkRegionalCorrection
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :
    GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
  (cmp99Eq389SignedCovariantLinkAmbientCorrection
      (L := L) (K := K) (Q := Q) P depth cell Omega rho U
      A c hc hAcoer).comp
    (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
      (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell))

/-- The right signed cutoff preserves the first-species amplitude and rate.
-/
theorem
    cmp99Eq389SignedCovariantLinkRegionalCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 A c hc hAcoer
      B0 delta0 (L ^ (depth + 1) : ℝ)) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq389SignedCovariantLinkRegionalCorrection
        (L := L) (K := K) (Q := Q) P depth cell Omega rho U
        A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K)
      delta0 := by
  exact finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
    (ι := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (κ := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (g := SUNLieCoord Nc)
    (cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell)
    (cmp99Eq389SignedCovariantLinkAmbientCorrection
      (L := L) (K := K) (Q := Q) P depth cell Omega rho U
      A c hc hAcoer)
    (fun source =>
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source)
    (cmp99Eq389SignedCovariantLinkAmbientCorrection_exponentialKernelBound
      (L := L) (K := K) (Q := Q) P depth cell Omega rho U
      A c hc hAcoer B0 delta0 C)

/-- A zero right signed cutoff kills one complete first-species cell on a
one-site source probe. -/
theorem
    cmp99Eq389SignedCovariantLinkRegionalCorrection_single_eq_zero_of_value_eq_zero
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (v : SUNLieCoord Nc)
    (hzero : cmp99SourceSeparatedSignedLargeBlockCutoff
      P L K Q depth cell source = 0) :
    cmp99Eq389SignedCovariantLinkRegionalCorrection
      (L := L) (K := K) (Q := Q) P depth cell Omega rho U
      A c hc hAcoer (singleFinitePiLp source v) = 0 := by
  unfold cmp99Eq389SignedCovariantLinkRegionalCorrection
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_single, hzero, zero_smul]
  have hsingle : singleFinitePiLp source (0 : SUNLieCoord Nc) = 0 := by
    apply PiLp.ext
    intro target
    by_cases htarget : target = source
    · subst target
      simp
    · rw [singleFinitePiLp_of_ne (0 : SUNLieCoord Nc) htarget]
      rfl
  rw [hsingle, map_zero]

/-- Sum of all complete signed first-species regional cells. -/
noncomputable def cmp99Eq389SignedCovariantLinkRegionalDefect
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c) :=
  ∑ cell, cmp99Eq389SignedCovariantLinkRegionalCorrection
    (L := L) (K := K) (Q := Q) P depth cell (Omega cell) rho U
    A c hc hAcoer

/-- The complete first species pays exactly the existing signed source
overlap `16`, independently of the total number of regional cells. -/
theorem
    cmp99Eq389SignedCovariantLinkRegionalDefect_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (Omega : FinBox 4 Q → ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hAcoer : IsCoerciveCLM A c)
    (B0 delta0 : ℝ)
    (C : ∀ cell, CMP99Eq342RegionalGreenCertificate (Omega cell) rho U 1
      A c hc hAcoer B0 delta0 (L ^ (depth + 1) : ℝ)) :
    FinitePiLpExponentialKernelBound
      (cmp99Eq389SignedCovariantLinkRegionalDefect
        (L := L) (K := K) (Q := Q) P depth Omega rho U
        A c hc hAcoer)
      (cmp99Eq342RescaledBlockDist
        (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
      (16 * cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K)
      delta0 := by
  unfold cmp99Eq389SignedCovariantLinkRegionalDefect
  apply finitePiLpExponentialKernelBound_sum_of_sourceOverlap
    (ι := FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (g := SUNLieCoord Nc) (n := FinBox 4 Q)
    (term := fun cell => cmp99Eq389SignedCovariantLinkRegionalCorrection
      (L := L) (K := K) (Q := Q) P depth cell (Omega cell) rho U
      A c hc hAcoer)
    (active := fun cell source =>
      cmp99SourceSeparatedSignedLargeBlockCutoff
        P L K Q depth cell source ≠ 0)
    (dist := cmp99Eq342RescaledBlockDist
      (cmp99SourceSeparatedLargeBlockSide L K depth) Q)
    (N := 16)
  · unfold cmp99Eq389SignedCovariantLinkSourceBudget
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (C default).B0_nonneg)
            P.derivBound_nonneg)
          (Nat.cast_nonneg K)))
      (add_nonneg zero_le_one (Real.exp_pos _).le)
  · exact (C default).delta0_pos
  · intro source
    simpa [cmp99SourceSeparatedSignedLargeBlockActiveCells] using
      card_cmp99SourceSeparatedSignedLargeBlockActiveCells_le_sixteen
        P L K Q depth source
  · intro cell source v hinactive
    apply
      cmp99Eq389SignedCovariantLinkRegionalCorrection_single_eq_zero_of_value_eq_zero
        (L := L) (K := K) (Q := Q) P depth cell (Omega cell) rho U
        A c hc hAcoer source v
    simpa using hinactive
  · intro cell
    exact
      cmp99Eq389SignedCovariantLinkRegionalCorrection_exponentialKernelBound
        (L := L) (K := K) (Q := Q) P depth cell (Omega cell) rho U
        A c hc hAcoer B0 delta0 (C cell)

end

end YangMills.RG
