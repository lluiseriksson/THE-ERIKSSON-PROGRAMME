/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixLeftDerivativeOwnerDecay
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
# PRE-VALIDATION: physical P8 Laplacian owner decay

This source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the Lean compiler.

It derives the per-depth Laplacian member of CMP99 (3.42) from the sealed
left-derivative owner bound.

The backward-divergence stencil has four directions.  The forward bond keeps
the target owner, while the backward bond costs one explicit
`exp ownerRate`.  The terminal factor `(ell * spacing)⁻¹` cancels the `ell`
in the left-derivative amplitude, so no carrier cardinality enters.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

theorem cmp96SourceSeparatedRegionalPrefixLaplacian_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a decay : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q)
    (root : ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) :
    letI : Nonempty (ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) := ⟨root⟩
    let ell := L ^ (depth + 1)
    let A := cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (ell : ℕ))
    let c := cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    let leftAmplitude := ownerAmplitude *
      ((1 + Real.exp ownerRate) / spacing)
    let laplacianAmplitude := 4 * leftAmplitude *
      ((1 + Real.exp ownerRate) / spacing)
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian
          (cmp96SourceSeparatedRegionalCell P L K Q depth cell)
          (matrixSUNAdjointModel Nc)
          (cmp99Eq389SourceSeparatedPhysicalBackground
            L K Q depth Nc background) ((ell : ℝ) * spacing)).comp
        (cmp96SourceSeparatedRegionalPrefixGreen
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth hspacing ha background budget fineSmall hsmall cell))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist laplacianAmplitude ownerRate := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let ell := L ^ (depth + 1)
  let Cregional := cmp96SourceSeparatedRegionalPrefixGreen
    P hL depth hspacing ha background budget fineSmall hsmall cell
  let A := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (ell : ℕ))
  let c := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let leftAmplitude := ownerAmplitude *
    ((1 + Real.exp ownerRate) / spacing)
  let laplacianAmplitude := 4 * leftAmplitude *
    ((1 + Real.exp ownerRate) / spacing)
  let terminalSpacing := (ell : ℝ) * spacing
  let regionalBackground := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let D := cmp99ActiveRegionSourceCovariantD0CLM Omega
    (matrixSUNAdjointModel Nc) regionalBackground terminalSpacing
  let Cleft := D.comp Cregional
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := ⟨root⟩
  have hc : 0 < c := by
    exact cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
        hspacing background budget fineSmall).le
      (Real.exp_pos _).le
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hterminal : 0 < terminalSpacing := mul_pos hell hspacing
  have hownerAmplitude : 0 ≤ ownerAmplitude := by
    exact mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  have hleftAmplitude : 0 ≤ leftAmplitude := by
    exact mul_nonneg hownerAmplitude
      (div_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le) hspacing.le)
  have hlaplacianAmplitude : 0 ≤ laplacianAmplitude := by
    exact mul_nonneg (mul_nonneg (by positivity) hleftAmplitude)
      (div_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le) hspacing.le)
  have hleft : FinitePiLpTypedBlockLocalizedSupBound Cleft
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftAmplitude * (ell : ℝ)) ownerRate := by
    simpa [Omega, ell, Cregional, A, c, rate, ownerRate, ownerAmplitude,
      leftAmplitude, terminalSpacing, regionalBackground, D, Cleft] using
      cmp96SourceSeparatedRegionalPrefixLeftDerivative_blockLocalizedSupBound
        P hL depth hspacing ha hdecay background budget fineSmall hsmall
        cell root
  refine ⟨hlaplacianAmplitude, mul_pos hell hrate, ?_⟩
  intro owner f hf target
  have hD := hleft.2.2 owner f hf
  have hforward (i : Fin 4) :
      ‖Cleft f ((target.1, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftAmplitude * (ell : ℝ)) *
          Real.exp (-(ownerRate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ))) * finitePiLpSupNorm f := by
    simpa [cmp99Eq342SourceLocalizedBondOwner,
      cmp99Eq342SourceLocalizedActiveOwner] using
      hD ((target.1, i) : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
  have hback (i : Fin 4) :
      ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftAmplitude * (ell : ℝ)) *
          (Real.exp ownerRate * Real.exp (-(ownerRate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ)))) * finitePiLpSupNorm f := by
    have hraw := hD ((target.1.shiftBack i, i) : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    have hshift := exp_neg_sourceLocalizationOwner_shiftBack_le_exp_mul
      L K Q depth target.1 owner i (delta := ownerRate)
        (mul_pos hell hrate).le
    calc
      ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftAmplitude * (ell : ℝ)) *
          Real.exp (-(ownerRate *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth
                (target.1.shiftBack i)) owner : ℝ))) *
          finitePiLpSupNorm f := by
            simpa [cmp99Eq342SourceLocalizedBondOwner] using hraw
      _ ≤ (leftAmplitude * (ell : ℝ)) *
          (Real.exp ownerRate * Real.exp (-(ownerRate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ)))) * finitePiLpSupNorm f := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshift
            (mul_nonneg hleftAmplitude hell.le))
          (finitePiLpSupNorm_nonneg f)
  change ‖cmp99ActiveRegionSourceCovariantLaplacian Omega
      (matrixSUNAdjointModel Nc) regionalBackground terminalSpacing
      (Cregional f) target‖ ≤ _
  rw [cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  change ‖cmp99GeneratedAmbientScaledCovariantLaplacian
      (matrixSUNAdjointModel Nc) regionalBackground terminalSpacing
      (extendZeroZeroCLM Omega (Cregional f)) target.1‖ ≤ _
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hterminal)]
  calc
    terminalSpacing⁻¹ *
        ‖∑ i : Fin 4,
          (Cleft f ((target.1, i) : PhysicalBond 4
              (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
            (matrixSUNAdjointModel Nc).adCLM
              (regionalBackground (positiveEdgeOfPhysicalBond
                ((target.1.shiftBack i, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
              (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))‖ ≤
      terminalSpacing⁻¹ * ∑ i : Fin 4,
        (‖Cleft f ((target.1, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
          ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
      calc
        ‖∑ i : Fin 4, _‖ ≤ ∑ i : Fin 4, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 4,
            (‖Cleft f ((target.1, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
              ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖) := by
          gcongr with i
          calc
            ‖Cleft f ((target.1, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
                (matrixSUNAdjointModel Nc).adCLM
                  (regionalBackground (positiveEdgeOfPhysicalBond
                    ((target.1.shiftBack i, i) : PhysicalBond 4
                      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
                  (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                    (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))))‖ ≤
              ‖Cleft f ((target.1, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
                ‖(matrixSUNAdjointModel Nc).adCLM
                  (regionalBackground (positiveEdgeOfPhysicalBond
                    ((target.1.shiftBack i, i) : PhysicalBond 4
                      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
                  (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                    (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))))‖ :=
                norm_sub_le _ _
            _ = _ := by rw [(matrixSUNAdjointModel Nc).norm_ad]
    _ ≤ terminalSpacing⁻¹ * ∑ _i : Fin 4,
        ((leftAmplitude * (ell : ℝ)) *
            Real.exp (-(ownerRate *
              (finBoxDist
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
                owner : ℝ))) * finitePiLpSupNorm f +
          (leftAmplitude * (ell : ℝ)) *
            (Real.exp ownerRate * Real.exp (-(ownerRate *
              (finBoxDist
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
                owner : ℝ)))) * finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
      exact Finset.sum_le_sum fun i _ => add_le_add (hforward i) (hback i)
    _ = laplacianAmplitude *
        Real.exp (-(ownerRate *
          (finBoxDist
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
            owner : ℝ))) * finitePiLpSupNorm f := by
      simp only [Finset.sum_const, Fintype.card_fin]
      dsimp [terminalSpacing, laplacianAmplitude]
      field_simp [ne_of_gt hspacing, ne_of_gt hell]
      ring

end

end YangMills.RG
