/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate
import YangMills.RG.BalabanCMP99Eq389SignedCovariantLinkPhysicalBound
import YangMills.RG.FinitePiLpBlockLocalizedSupAlgebra

/-!
# PRE-VALIDATION: source-localized first species of CMP99 (3.89)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

This module applies the literal left-derivative Green estimate of CMP99
(3.42) to an arbitrary field supported in one source-localization block.  It
then uses the exact signed-cutoff slope and one-step owner geometry to obtain
the first species of (3.89), with its `K^-1` gain present before the cell sum.

No coordinate-probe expansion, Schur bound, or reciprocal coercivity enters.
The result is one regional cell before overlap summation.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq389SourceLocalizedFirstAmbientSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

private instance instNeZeroEq389SourceLocalizedFirstOwnerSide
    (K Q : ℕ) [NeZero K] [NeZero Q] :
    NeZero (2 * (K * Q)) :=
  ⟨(Nat.mul_pos (by omega)
    (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q))).ne'⟩

private instance instNeZeroEq389SourceLocalizedFirstFineSide
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (L ^ (depth + 1) * (2 * (K * Q))) :=
  ⟨(Nat.mul_pos (pow_pos (NeZero.pos L) (depth + 1))
    (Nat.mul_pos (by omega)
      (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q)))).ne'⟩

private theorem finBoxEquivCast_shiftBack
    {d N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (x : FinBox d N) (i : Fin d) :
    Equiv.cast (congrArg (FinBox d) h) (x.shiftBack i) =
      (Equiv.cast (congrArg (FinBox d) h) x).shiftBack i := by
  subst M
  rfl

/-- A backward fine step costs at most one `exp(delta)` in the literal
source-localization owner metric, uniformly for every selected owner fibre.
-/
theorem exp_neg_sourceLocalizationOwner_shiftBack_le_exp_mul
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (owner : FinBox 4 (2 * (K * Q))) (i : Fin 4)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Real.exp (-(delta *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
          owner : ℝ))) ≤
      Real.exp delta * Real.exp (-(delta *
        (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
          owner : ℝ))) := by
  have hstep := finBoxDist_blockSite_shiftBack_le_one
    (m := L ^ (depth + 1)) (n := 2 * (K * Q))
    (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x) i
  have hcastShift :
      cmp99Eq389SourceLocalizationSiteEquiv L K Q depth (x.shiftBack i) =
        (cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x).shiftBack i := by
    exact finBoxEquivCast_shiftBack
      (cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth)
      x i
  rw [← hcastShift] at hstep
  have hdist :
      finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x) owner ≤
        1 + finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
          owner :=
    (finBoxDist_triangle
      (cmp99Eq389SourceLocalizationOwner L K Q depth x)
      (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
      owner).trans (Nat.add_le_add_right hstep _)
  have hdistR :
      (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
          owner : ℝ) ≤
        1 + (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
          owner : ℝ) := by
    exact_mod_cast hdist
  have harg :
      -(delta * (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
          owner : ℝ)) ≤
        delta + -(delta *
          (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
            owner : ℝ)) := by
    nlinarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr harg

/-- One literal signed covariant-link cell obeys the source-localized
supremum estimate, with the exact `K^-1` amplitude before overlap summation.
-/
theorem cmp99Eq389SignedCovariantLinkRegionalCorrection_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile) (depth : ℕ)
    (cell : FinBox 4 Q)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
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
    (C : CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth Omega rho U 1 A c hc hAcoer B0 delta0) :
    FinitePiLpTypedBlockLocalizedSupBound
      (ι := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
      (β := FinBox 4 (2 * (K * Q)))
      (g := SUNLieCoord Nc)
      (cmp99Eq389SignedCovariantLinkRegionalCorrection
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P depth cell Omega rho U
        A c hc hAcoer)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      finBoxDist
      (cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K)
      delta0 := by
  let hcutoff : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℝ :=
    cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell
  let slope := cmp99Eq389SignedCovariantLinkSlopeBudget P L K depth
  have hslope : 0 ≤ slope :=
    cmp99Eq389SignedCovariantLinkSlopeBudget_nonneg P L K depth
  have hcutoff_le : ∀ source, ‖hcutoff source‖ ≤ 1 := by
    intro source
    exact
      (cmp99SourceSeparatedSignedLargeBlockSquarePartition
        (L := L) (K := K) (Q := Q) (depth := depth) P).norm_value_le_one
          cell source
  let DG : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      GaugeOneCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) :=
    (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U 1).comp
      (cmp99RegionalDirichletGreen Omega A hc hAcoer)
  have hDG : FinitePiLpTypedBlockLocalizedSupBound
      (DG.comp (restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega))
      (cmp99Eq389SourceLocalizationOwner L K Q depth)
      (fun b : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
          cmp99Eq389SourceLocalizationOwner L K Q depth b.1)
      finBoxDist (B0 * (L ^ (depth + 1) : ℝ)) delta0 := by
    apply finitePiLpTypedBlockLocalizedSupBound_comp_restrictZeroCLM_right
    simpa [DG, cmp99Eq342SourceLocalizedActiveOwner,
      cmp99Eq342SourceLocalizedBondOwner] using C.left_derivative_bound
  have hDGCut :=
    finitePiLpTypedBlockLocalizedSupBound_comp_scalarMultiplier_right
      hcutoff (DG.comp (restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega))
      hcutoff_le hDG
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
  intro owner f hf x
  let cutField := finitePiLpScalarMultiplier
    (g := SUNLieCoord Nc) hcutoff f
  let phi : PhysicalGaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc :=
    extendZeroZeroCLM Omega
      (cmp99RegionalDirichletGreen Omega A hc hAcoer
        (restrictZeroCLM Omega cutField))
  have hforwardD (i : Fin 4) :
      ‖covariantD0CLM rho U phi
          ((x, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (B0 * (L ^ (depth + 1) : ℝ)) *
          Real.exp (-(delta0 *
            (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
              owner : ℝ))) * finitePiLpSupNorm f := by
    have hD := hDGCut.2.2 owner f hf
      ((x, i) : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    simpa [DG, cutField, phi, cmp99ActiveRegionSourceCovariantD0CLM,
      ContinuousLinearMap.comp_apply] using hD
  have hbackD (i : Fin 4) :
      ‖covariantD0CLM rho U phi
          ((x.shiftBack i, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (B0 * (L ^ (depth + 1) : ℝ)) *
          (Real.exp delta0 * Real.exp (-(delta0 *
            (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
              owner : ℝ)))) * finitePiLpSupNorm f := by
    have hD := hDGCut.2.2 owner f hf
      ((x.shiftBack i, i) : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    calc
      ‖covariantD0CLM rho U phi
          ((x.shiftBack i, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (B0 * (L ^ (depth + 1) : ℝ)) *
          Real.exp (-(delta0 *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth (x.shiftBack i))
              owner : ℝ))) * finitePiLpSupNorm f := by
        simpa [DG, cutField, phi, cmp99ActiveRegionSourceCovariantD0CLM,
          ContinuousLinearMap.comp_apply] using hD
      _ ≤ (B0 * (L ^ (depth + 1) : ℝ)) *
          (Real.exp delta0 * Real.exp (-(delta0 *
            (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
              owner : ℝ)))) * finitePiLpSupNorm f := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · exact exp_neg_sourceLocalizationOwner_shiftBack_le_exp_mul
              L K Q depth x owner i C.delta0_pos.le
          · exact mul_nonneg C.B0_nonneg (by positivity)
        · exact finitePiLpSupNorm_nonneg f
  change ‖cmp99Eq389SignedCovariantLinkAmbientOperator
      (L := L) (K := K) (Q := Q) P depth cell rho U
      (cmp99RegionalExtendedDirichletGreen Omega A hc hAcoer cutField) x‖ ≤ _
  rw [cmp99Eq389SignedCovariantLinkAmbientOperator_apply]
  change ‖cmp99CovariantCutoffLinkDerivative rho U 1 hcutoff phi x‖ ≤ _
  calc
    ‖cmp99CovariantCutoffLinkDerivative rho U 1 hcutoff phi x‖ ≤
        slope * ∑ i : Fin 4,
          (‖covariantD0CLM rho U phi
              ((x, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
            ‖covariantD0CLM rho U phi
              ((x.shiftBack i, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖) :=
      norm_cmp99CovariantCutoffLinkDerivative_one_le rho U hcutoff phi x
        slope
        (fun i => norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shift_le
          (L := L) (K := K) (Q := Q) P depth cell x i)
        (fun i =>
          norm_cmp99SourceSeparatedSignedLargeBlockCutoff_sub_shiftBack_le
            (L := L) (K := K) (Q := Q) P depth cell x i)
    _ ≤ slope * ∑ _i : Fin 4,
        ((B0 * (L ^ (depth + 1) : ℝ)) *
              Real.exp (-(delta0 *
                (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
                  owner : ℝ))) * finitePiLpSupNorm f +
          (B0 * (L ^ (depth + 1) : ℝ)) *
              (Real.exp delta0 * Real.exp (-(delta0 *
                (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
                  owner : ℝ)))) * finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_left _ hslope
      apply Finset.sum_le_sum
      intro i _hi
      exact add_le_add (hforwardD i) (hbackD i)
    _ = cmp99Eq389SignedCovariantLinkSourceBudget P B0 delta0 K *
        Real.exp (-(delta0 *
          (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
            owner : ℝ))) * finitePiLpSupNorm f := by
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
              (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
                owner : ℝ))) * finitePiLpSupNorm f := by ring
        _ = 4 * ((8 * B0 * P.derivBound) / (K : ℝ)) *
            (1 + Real.exp delta0) *
            Real.exp (-(delta0 *
              (finBoxDist (cmp99Eq389SourceLocalizationOwner L K Q depth x)
                owner : ℝ))) * finitePiLpSupNorm f := by
          rw [hscale]

end

end YangMills.RG
