import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepth

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]
variable (OmegaSource : ActiveGaugeRegion 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)))
variable (regions : CMP99SourceActiveRegionChain 4 L
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) OmegaSource 0)
variable (hL : 2 ≤ L)
variable {spacing epsilon : ℝ}
variable (background : GaugeConfig 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)) (SUN Nc))
variable (chain : CMP99SourceUbarRadiusChain 4 L Nc 0 epsilon)
variable (fineSmall : ∀ e : ConcreteEdge 4
  (cmp99SourceSeparatedLargeBlockSide L K 0 * (2 * Q)),
  ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)

/-- Per-depth-zero value action for every source owner.  The explicit root
supplies only the nonempty carrier instance. -/
theorem
    cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_blockLocalizedSupBound
    (hspacing : 0 < spacing)
    {decay : ℝ} (hdecay : 0 < decay)
    (root : ActiveGaugeRegion.Site OmegaSource) :
    letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
    let ell := L ^ (0 + 1)
    let A :=
      cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
        (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
        regions hL background chain fineSmall decay
    let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
      (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
        (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
        regions hL background chain fineSmall hspacing)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q 0)
      finBoxDist (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate := by
  dsimp only
  let ell := L ^ (0 + 1)
  let A :=
    cmp99Eq360C6dSourceSeparatedAmbientPrecisionDecayAmplitude_zero
      (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
      regions hL background chain fineSmall decay
  let c := cmp99Eq360C6dSourceSeparatedZeroDepthCoercivity
    (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
    regions hL background chain fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let G := cmp99Eq360C6dSourceSeparatedAmbientGreen_zero
    (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
    regions hL background chain fineSmall hspacing
  letI : Nonempty (ActiveGaugeRegion.Site OmegaSource) := ⟨root⟩
  have hA : 0 ≤ A := by
    exact
      (cmp99Eq360C6dSourceSeparatedAmbientPrecision_zero_exponentialKernelBound
        (Nc := Nc) (OmegaSource := OmegaSource) (spacing := spacing)
        regions hL background chain fineSmall hspacing hdecay).1
  have hc : 0 < c := by
    exact cmp99SourceActiveRegionFullCompanionCountingCoefficient_pos_zero
      regions (by norm_num : 2 ≤ 4) hL hspacing background chain fineSmall
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (0 + 1)
  have hownerAmplitude : 0 ≤ ownerAmplitude := by
    exact mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  refine ⟨mul_nonneg hownerAmplitude (sq_nonneg _),
    mul_pos hell hrate, ?_⟩
  intro owner f hf target
  by_cases howner : ∃ source : ActiveGaugeRegion.Site OmegaSource,
      cmp99Eq342SourceLocalizedActiveOwner L K Q 0 source = owner
  · rcases howner with ⟨source, hsource⟩
    have hbase :=
      norm_cmp99Eq360C6dSourceSeparatedAmbientGreen_zero_apply_le_ownerScale
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        OmegaSource regions hL background chain fineSmall
        hspacing hdecay owner source hsource f hf target
    simpa [G, ell, A, c, rate, ownerRate, ownerAmplitude,
      finBoxDist_comm] using hbase
  · have hfzero : f = 0 := by
      apply PiLp.ext
      intro source
      apply hf source
      intro hsource
      exact howner ⟨source, hsource⟩
    subst f
    have hzero : G (0 : ActiveGaugeZeroCochain OmegaSource (SUNLieCoord Nc))
        target = 0 := by
      simp only [map_zero, PiLp.zero_apply]
    rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hownerAmplitude (sq_nonneg _))
        (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg 0)

end

end YangMills.RG
