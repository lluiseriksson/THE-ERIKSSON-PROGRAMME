/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixGreenBlockLocalizedOwnerDecay
import YangMills.RG.BalabanCMP99ActiveRegionSourceCovariantAdjointStencil
import YangMills.RG.BalabanCMP99Eq389ThreeSpeciesPhysicalBound
import YangMills.RG.FinitePiLpBlockLocalizedSupOwnerKernelComposition
import YangMills.RG.BalabanCMP99SourcePi4Collar

/-!
# PRE-VALIDATION: physical right-adjoint member of CMP99 (3.42)

This source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the Lean compiler.

The input derivative is expanded through the literal regional backward
divergence.  It is not inferred from the left-derivative estimate by abstract
adjunction.  The resulting field has owner radius one, and the complete
radius-one owner ball is bounded by `3^4 = 81` before applying the physical
Green estimate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

theorem cmp96SourceSeparatedRegionalPrefixRightAdjoint_blockLocalizedSupBound
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
    let rightAmplitude :=
      648 * ownerAmplitude * Real.exp ownerRate / spacing
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp96SourceSeparatedRegionalPrefixGreen
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth hspacing ha background budget fineSmall hsmall cell).comp
        (cmp99ActiveRegionSourceCovariantD0CLM
          (cmp96SourceSeparatedRegionalCell P L K Q depth cell)
          (matrixSUNAdjointModel Nc)
          (cmp99Eq389SourceSeparatedPhysicalBackground
            L K Q depth Nc background)
          ((ell : ℝ) * spacing)).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (rightAmplitude * (ell : ℝ)) ownerRate := by
  dsimp only
  classical
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
  let terminalSpacing := (ell : ℝ) * spacing
  let regionalBackground := cmp99Eq389SourceSeparatedPhysicalBackground
    L K Q depth Nc background
  let D := cmp99ActiveRegionSourceCovariantD0CLM Omega
    (matrixSUNAdjointModel Nc) regionalBackground terminalSpacing
  let rightCoefficient :
      FinBox 4 (2 * (K * Q)) → FinBox 4 (2 * (K * Q)) → ℝ :=
    fun middle source =>
      if finBoxDist middle source ≤ 1 then 8 / terminalSpacing else 0
  let rightAmplitude :=
    648 * ownerAmplitude * Real.exp ownerRate / spacing
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
  have hrate : 0 < rate :=
    finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hterminal : 0 < terminalSpacing := mul_pos hell hspacing
  have hownerAmplitude : 0 ≤ ownerAmplitude :=
    mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  have hvalue : FinitePiLpTypedBlockLocalizedSupBound Cregional
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate := by
    simpa [Omega, ell, Cregional, A, c, rate, ownerRate, ownerAmplitude] using
      cmp96SourceSeparatedRegionalPrefixGreen_blockLocalizedSupBound
        P hL depth hspacing ha hdecay background budget fineSmall hsmall
        cell root
  have hright : FinitePiLpTypedOwnerSupKernelBound D.adjoint
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      rightCoefficient := by
    refine ⟨?_, ?_⟩
    · intro middle source
      dsimp [rightCoefficient]
      split_ifs <;> positivity
    · intro source f hf middle
      by_cases hnear : finBoxDist middle source ≤ 1
      · rw [show rightCoefficient middle source = 8 / terminalSpacing by
          simp [rightCoefficient, hnear]]
        calc
          finitePiLpSupNorm
              (finitePiLpOwnerPart
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
                middle (D.adjoint f)) ≤
            finitePiLpSupNorm (D.adjoint f) :=
              finitePiLpSupNorm_ownerPart_le
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
                middle (D.adjoint f)
          _ ≤ (2 * 4 / terminalSpacing) * finitePiLpSupNorm f := by
            exact
              finitePiLpSupNorm_cmp99ActiveRegionSourceCovariantD0CLM_adjoint_le
                Omega (matrixSUNAdjointModel Nc) regionalBackground
                hterminal f
          _ = (8 / terminalSpacing) * finitePiLpSupNorm f := by ring
      · have hpart : finitePiLpOwnerPart
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
            middle (D.adjoint f) = 0 := by
          apply PiLp.ext
          intro x
          rw [finitePiLpOwnerPart_apply]
          by_cases hx :
              cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = middle
          · rw [if_pos hx]
            apply
              cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply_eq_zero_of_owner_far
                depth Omega (matrixSUNAdjointModel Nc) regionalBackground
                terminalSpacing source f hf x
            simpa [hx] using hnear
          · rw [if_neg hx]
        rw [hpart]
        have hzero : finitePiLpSupNorm
            (0 : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) = 0 := by
          apply le_antisymm
          · apply finitePiLpSupNorm_le_of_norm_apply_le
            intro x
            simp
          · exact finitePiLpSupNorm_nonneg 0
        rw [hzero]
        simp [rightCoefficient, hnear]
  have hconvolution : ∀ target source,
      finiteOwnerKernelConvolution
          (finiteOwnerExponentialCoefficient finBoxDist
            (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate)
          rightCoefficient target source ≤
        (rightAmplitude * (ell : ℝ)) *
          Real.exp (-(ownerRate * (finBoxDist target source : ℝ))) := by
    intro target source
    let near : Finset (FinBox 4 (2 * (K * Q))) :=
      Finset.univ.filter fun middle => finBoxDist middle source ≤ 1
    have hcard : near.card ≤ 81 := by
      have hball := finBoxDist_ball_card_le_two_mul_add_one_pow source 1
      have : near.card ≤ (2 * 1 + 1) ^ 4 := by
        simpa [near, finBoxDist_comm] using hball
      norm_num at this ⊢
      exact this
    have hterm : ∀ middle ∈ near,
        (ownerAmplitude * (ell : ℝ) ^ 2) *
              Real.exp (-(ownerRate * (finBoxDist target middle : ℝ))) *
            (8 / terminalSpacing) ≤
          ((ownerAmplitude * (ell : ℝ) ^ 2) * Real.exp ownerRate *
              (8 / terminalSpacing)) *
            Real.exp (-(ownerRate * (finBoxDist target source : ℝ))) := by
      intro middle hmiddle
      have hnear : finBoxDist middle source ≤ 1 := by
        simpa [near] using (Finset.mem_filter.mp hmiddle).2
      have hdist : finBoxDist target source ≤
          finBoxDist target middle + 1 :=
        (finBoxDist_triangle target middle source).trans
          (Nat.add_le_add_left hnear _)
      have hdistR : (finBoxDist target source : ℝ) ≤
          (finBoxDist target middle : ℝ) + 1 := by exact_mod_cast hdist
      have harg :
          -(ownerRate * (finBoxDist target middle : ℝ)) ≤
            ownerRate +
              -(ownerRate * (finBoxDist target source : ℝ)) := by
        nlinarith [mul_pos hell hrate]
      have hexp :
          Real.exp (-(ownerRate * (finBoxDist target middle : ℝ))) ≤
            Real.exp ownerRate *
              Real.exp (-(ownerRate * (finBoxDist target source : ℝ))) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr harg
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hownerAmplitude (sq_nonneg _)))
        (div_nonneg (by positivity) hterminal.le)
    calc
      finiteOwnerKernelConvolution
          (finiteOwnerExponentialCoefficient finBoxDist
            (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate)
          rightCoefficient target source =
        ∑ middle ∈ near,
          ((ownerAmplitude * (ell : ℝ) ^ 2) *
              Real.exp (-(ownerRate * (finBoxDist target middle : ℝ)))) *
            (8 / terminalSpacing) := by
          simp [finiteOwnerKernelConvolution,
            finiteOwnerExponentialCoefficient, rightCoefficient, near]
      _ ≤ ∑ _middle ∈ near,
          ((ownerAmplitude * (ell : ℝ) ^ 2) * Real.exp ownerRate *
              (8 / terminalSpacing)) *
            Real.exp (-(ownerRate * (finBoxDist target source : ℝ))) := by
          exact Finset.sum_le_sum hterm
      _ = (near.card : ℝ) *
          (((ownerAmplitude * (ell : ℝ) ^ 2) * Real.exp ownerRate *
              (8 / terminalSpacing)) *
            Real.exp (-(ownerRate * (finBoxDist target source : ℝ)))) := by
          simp
      _ ≤ (81 : ℝ) *
          (((ownerAmplitude * (ell : ℝ) ^ 2) * Real.exp ownerRate *
              (8 / terminalSpacing)) *
            Real.exp (-(ownerRate * (finBoxDist target source : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard
          · positivity
      _ = (rightAmplitude * (ell : ℝ)) *
          Real.exp (-(ownerRate * (finBoxDist target source : ℝ))) := by
          dsimp [rightAmplitude, terminalSpacing]
          field_simp [ne_of_gt hspacing, ne_of_gt hell]
          ring
  exact finitePiLpTypedBlockLocalizedSupBound_comp_of_ownerKernel
    Cregional D.adjoint
    (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
    (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
    (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
    finBoxDist rightCoefficient hvalue hright
    (mul_nonneg
      (mul_nonneg (by positivity) hownerAmplitude)
      (mul_nonneg (Real.exp_pos _).le (div_nonneg (by positivity) hspacing.le)))
    hconvolution

end

end YangMills.RG

