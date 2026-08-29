import YangMills.RG.BalabanCMP99ActiveRegionSourceCovariantAdjointStencil
import YangMills.RG.FinitePiLpBlockLocalizedSupOwnerKernelComposition
import YangMills.RG.BalabanCMP99SourcePi4Collar

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Localized right-adjoint derivative from a Green value bound

This is the reusable algebraic/stencil step behind the third CMP99 (3.42)
action.  It expands the literal backward divergence and never infers the
result from abstract adjoint symmetry.  Its radius-one owner ball has the
visible bound `3^4 = 81`; together with the eight stencil terms this gives
the displayed coefficient `648`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A localized Green value estimate yields the literal right-adjoint
derivative estimate.  The Green and background remain explicit parameters;
the physical C6d specialization must provide both by name. -/
theorem cmp99Eq342_rightAdjoint_blockLocalizedSupBound_of_value
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {spacing ell A rate : ℝ}
    (hspacing : 0 < spacing) (hell : 0 < ell)
    (hG : FinitePiLpTypedBlockLocalizedSupBound G
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (A * ell ^ 2) rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      (G.comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background (ell * spacing)).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      ((648 * A * Real.exp rate / spacing) * ell) rate := by
  classical
  let terminalSpacing := ell * spacing
  let D := cmp99ActiveRegionSourceCovariantD0CLM Omega
    (matrixSUNAdjointModel Nc) background terminalSpacing
  let rightCoefficient :
      FinBox 4 (2 * (K * Q)) → FinBox 4 (2 * (K * Q)) → ℝ :=
    fun middle source =>
      if finBoxDist middle source ≤ 1 then 8 / terminalSpacing else 0
  let rightAmplitude := 648 * A * Real.exp rate / spacing
  have hrate : 0 < rate := hG.2.1
  have hterminal : 0 < terminalSpacing := mul_pos hell hspacing
  have hAell : 0 ≤ A * ell ^ 2 := hG.1
  have hA : 0 ≤ A := by
    exact nonneg_of_mul_nonneg_left hAell (sq_pos_of_pos hell)
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
                Omega (matrixSUNAdjointModel Nc) background
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
                depth Omega (matrixSUNAdjointModel Nc) background
                terminalSpacing source f hf x
            simpa [hx] using hnear
          · simp [if_neg hx]
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
            (A * ell ^ 2) rate)
          rightCoefficient target source ≤
        (rightAmplitude * ell) *
          Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
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
        (A * ell ^ 2) *
              Real.exp (-(rate * (finBoxDist target middle : ℝ))) *
            (8 / terminalSpacing) ≤
          ((A * ell ^ 2) * Real.exp rate *
              (8 / terminalSpacing)) *
            Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
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
          -(rate * (finBoxDist target middle : ℝ)) ≤
            rate + -(rate * (finBoxDist target source : ℝ)) := by
        nlinarith
      have hexp :
          Real.exp (-(rate * (finBoxDist target middle : ℝ))) ≤
            Real.exp rate *
              Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr harg
      have hcoefficient : 0 ≤ (8 : ℝ) / terminalSpacing :=
        div_nonneg (by norm_num) hterminal.le
      calc
        (A * ell ^ 2) *
              Real.exp (-(rate * (finBoxDist target middle : ℝ))) *
            (8 / terminalSpacing) ≤
          ((A * ell ^ 2) *
              (Real.exp rate *
                Real.exp (-(rate * (finBoxDist target source : ℝ))))) *
            (8 / terminalSpacing) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hexp hAell) hcoefficient
        _ = ((A * ell ^ 2) * Real.exp rate *
                (8 / terminalSpacing)) *
              Real.exp (-(rate * (finBoxDist target source : ℝ))) := by ring
    calc
      finiteOwnerKernelConvolution
          (finiteOwnerExponentialCoefficient finBoxDist
            (A * ell ^ 2) rate)
          rightCoefficient target source =
        ∑ middle ∈ near,
          ((A * ell ^ 2) *
              Real.exp (-(rate * (finBoxDist target middle : ℝ)))) *
            (8 / terminalSpacing) := by
          simp [finiteOwnerKernelConvolution,
            finiteOwnerExponentialCoefficient, rightCoefficient, near]
          rw [Finset.sum_filter]
      _ ≤ ∑ _middle ∈ near,
          ((A * ell ^ 2) * Real.exp rate *
              (8 / terminalSpacing)) *
            Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
          exact Finset.sum_le_sum hterm
      _ = (near.card : ℝ) *
          (((A * ell ^ 2) * Real.exp rate *
              (8 / terminalSpacing)) *
            Real.exp (-(rate * (finBoxDist target source : ℝ)))) := by
          simp
      _ ≤ (81 : ℝ) *
          (((A * ell ^ 2) * Real.exp rate *
              (8 / terminalSpacing)) *
            Real.exp (-(rate * (finBoxDist target source : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard
          · positivity
      _ = (rightAmplitude * ell) *
          Real.exp (-(rate * (finBoxDist target source : ℝ))) := by
          dsimp [rightAmplitude, terminalSpacing]
          field_simp [ne_of_gt hspacing, ne_of_gt hell]
          ring
  have hrightAmplitude : 0 ≤ rightAmplitude := by
    dsimp [rightAmplitude]
    positivity
  exact finitePiLpTypedBlockLocalizedSupBound_comp_of_ownerKernel
    G D.adjoint
    (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
    (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
    (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
    finBoxDist rightCoefficient hG hright
    (mul_nonneg hrightAmplitude hell.le)
    hconvolution

end

end YangMills.RG
