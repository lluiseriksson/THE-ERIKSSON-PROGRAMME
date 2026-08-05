/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition
import YangMills.RG.BalabanCMP99SourceEq395FirstLeftWeightedRow
import YangMills.RG.FinitePiLpExponentialInverseDecay
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# The physical single-cell regional correction in CMP99 (3.88)

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler-verified.

For every source large-block cell this file constructs the Dirichlet region
as the exact finite-range thickening of the physical cutoff support.  The
regional Green is the canonical inverse of the compression of the one
ambient generated precision; it is not supplied by the caller and is not
identified with a separately chosen global Green.

Combes--Thomas decay is transported first to the compressed precision and
then to its canonical inverse.  The already sealed physical commutator is
composed with that regional Green and the contractive right cutoff.  The
result retains one explicit, volume-independent cell amplitude.  Summing the
cells and proving the defect contraction remain the next brick.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

private instance instNeZeroSourceRegionalLargeBlockSide
    (M depth : ℕ) [NeZero M] :
    NeZero (cmp99SourceRegionalLargeBlockSide M depth) :=
  ⟨by
    unfold cmp99SourceRegionalLargeBlockSide
    exact (pow_pos (NeZero.pos M) (depth + 2)).ne'⟩

private instance instNeZeroSourceRegionalAmbientSide
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    NeZero (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (pow_pos (NeZero.pos M) (depth + 2))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- Every member of an exact real square partition is pointwise contractive.
This is derived from `square_sum`; no second cutoff bound is stored. -/
theorem CMP99RegionalFineSquarePartition.norm_value_le_one
    {m q : ℕ} [NeZero m] [NeZero q]
    (P : CMP99RegionalFineSquarePartition m q)
    (cell : FinBox 4 q) (x : FinBox 4 (m * (2 * q))) :
    ‖P.value cell x‖ ≤ 1 := by
  classical
  have hterm : P.value cell x ^ 2 ≤
      ∑ c : FinBox 4 q, P.value c x ^ 2 := by
    exact Finset.single_le_sum (fun c _ => sq_nonneg (P.value c x))
      (Finset.mem_univ cell)
  rw [P.square_sum x] at hterm
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs, one_pow] using hterm

/-- The four-dimensional shell estimate is uniform in the side of the
periodic box.  Keeping that side arbitrary avoids silently rewriting a
physical side `M^(depth+2) * (2*Q)` as a box of the special form `2*Q'`. -/
theorem finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound_any
    {N : ℕ} [NeZero N] (source : FinBox 4 N)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑ target : FinBox 4 N,
      Real.exp (-(sigma * (finBoxDist target source : ℝ))) ≤
        cmp99OmegaSiteExpSumBound sigma := by
  unfold cmp99OmegaSiteExpSumBound
  have hN : ∀ k,
      ((Finset.univ.filter
        (fun target : FinBox 4 N =>
          finBoxDist target source = k)).card : ℝ) ≤
        (((2 * k + 1) ^ 4 : ℕ) : ℝ) := by
    intro k
    exact_mod_cast (Finset.card_le_card
      (show Finset.univ.filter
          (fun target : FinBox 4 N => finBoxDist target source = k) ⊆
        Finset.univ.filter (fun target => finBoxDist source target ≤ k) by
        intro target htarget
        rw [Finset.mem_filter] at htarget ⊢
        exact ⟨htarget.1, by simpa [finBoxDist_comm] using htarget.2.le⟩)).trans
          (finBoxDist_ball_card_le_two_mul_add_one_pow source k)
  have hsummable : Summable
      (fun k : ℕ => (((2 * k + 1) ^ 4 : ℕ) : ℝ) *
        Real.exp (-sigma * (k : ℝ))) := by
    simpa only [neg_mul] using summable_cmp99OmegaSiteExpSumBound hsigma
  simpa only [neg_mul] using
    (lattice_exp_sum_le_of_shell
      (fun target : FinBox 4 N => finBoxDist target source)
      (σ := sigma) (fun k => (((2 * k + 1) ^ 4 : ℕ) : ℝ))
      hN hsummable)

/-- Same-carrier specialization of exponential-kernel composition on an
arbitrary four-dimensional periodic box.  The physical callers therefore do
not ask elaboration to infer three copies of a large generated carrier. -/
theorem finitePiLpExponentialKernelBound_comp_finBox
    {N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]
    {A B rate sigma : ℝ} (hsigma : 0 < sigma) (hsigmaRate : sigma < rate)
    (Left Right : GaugeZeroCochain 4 N g →L[ℝ] GaugeZeroCochain 4 N g)
    (hLeft : FinitePiLpExponentialKernelBound Left finBoxDist A rate)
    (hRight : FinitePiLpExponentialKernelBound Right finBoxDist B rate) :
    FinitePiLpExponentialKernelBound (Left.comp Right) finBoxDist
      (A * B * cmp99OmegaSiteExpSumBound sigma) (rate - sigma) := by
  have hS : 0 ≤ cmp99OmegaSiteExpSumBound sigma := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  exact finitePiLpTypedExponentialKernelBound_comp
    (ι := FinBox 4 N) (κ := FinBox 4 N) (ν := FinBox 4 N) (g := g)
    (A := A) (B := B) (rate := rate) (sigma := sigma)
    (S := cmp99OmegaSiteExpSumBound sigma)
    finBoxDist finBoxDist finBoxDist
    (fun target middle source => finBoxDist_triangle target middle source)
    hsigma hsigmaRate hS
    (fun target => by
      simpa [finBoxDist_comm] using
        finBoxDist_exp_sum_le_cmp99OmegaSiteExpSumBound_any target hsigma)
    Left Right hLeft hRight

/-- Exponential localization of an ambient kernel descends exactly to its
Dirichlet compression. -/
theorem cmp99RegionalDirichletPrecision_exponentialKernelBound
    {m q : ℕ} [NeZero m] [NeZero q]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
      [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (K : GaugeZeroCochain 4 (m * (2 * q)) g →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) g)
    {A rate : ℝ}
    (hK : FinitePiLpExponentialKernelBound K
      (finBoxDist : FinBox 4 (m * (2 * q)) →
        FinBox 4 (m * (2 * q)) → ℕ) A rate) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalDirichletPrecision Omega K)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1) A rate := by
  refine ⟨hK.1, hK.2.1, ?_⟩
  intro source target v
  have hext :
      extendZeroZeroCLM Omega (singleFinitePiLp source v) =
        singleFinitePiLp source.1 v := by
    apply PiLp.ext
    intro x
    by_cases hx : x ∈ Omega.sites
    · rw [extendZeroZeroCLM_apply_of_mem Omega _ x hx]
      by_cases hxs : x = source.1
      · subst x
        simp
      · have hsub : (⟨x, hx⟩ : ActiveGaugeRegion.Site Omega) ≠ source := by
          intro heq
          exact hxs (congrArg Subtype.val heq)
        rw [singleFinitePiLp_of_ne v hsub,
          singleFinitePiLp_of_ne v hxs]
    · rw [extendZeroZeroCLM_apply_of_not_mem Omega _ x hx]
      have hxs : x ≠ source.1 := by
        intro heq
        apply hx
        simpa [heq] using source.2
      rw [singleFinitePiLp_of_ne v hxs]
  change ‖K (extendZeroZeroCLM Omega (singleFinitePiLp source v)) target.1‖ ≤ _
  rw [hext]
  exact hK.2.2 source.1 target.1 v

/-- Canonical inverse decay for an arbitrary compressed regional precision.
The only analytic inputs are localization and coercivity of the one ambient
operator. -/
theorem cmp99RegionalDirichletGreen_exponentialKernelBound
    {m q : ℕ} [NeZero m] [NeZero q]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
      [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (K : GaugeZeroCochain 4 (m * (2 * q)) g →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) g)
    {A decay c : ℝ} (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (hK : FinitePiLpExponentialKernelBound K
      (finBoxDist : FinBox 4 (m * (2 * q)) →
        FinBox 4 (m * (2 * q)) → ℕ) A decay) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalDirichletGreen Omega K hc hKcoer)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (2 / c)
      (finitePiLpExponentialInverseDecayRate A decay
        (cmp99OmegaSiteExpSumBound (decay / 4)) c) := by
  apply finitePiLpExponentialKernelBound_inverse_canonical
    (fun target source : ActiveGaugeRegion.Site Omega =>
      finBoxDist target.1 source.1)
    (fun p q => finBoxDist_comm p.1 q.1)
    (fun p q r => finBoxDist_triangle p.1 q.1 r.1)
    (fun p => finBoxDist_self p.1)
    (cmp99RegionalDirichletPrecision Omega K)
    (cmp99RegionalDirichletGreen Omega K hc hKcoer)
    hK.2.1 hc
  · unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  · exact cmp99RegionalDirichletPrecision_exponentialKernelBound
      Omega K hK
  · exact isCoerciveCLM_cmp99RegionalDirichletPrecision Omega K hKcoer
  · exact cmp99RegionalDirichletPrecision_comp_green Omega K hc hKcoer
  · intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le Omega target
      (div_pos hK.2.1 (by norm_num))

/-- Zero extension of a regional exponentially localized kernel preserves
the same amplitude and rate on the ambient metric. -/
theorem cmp99RegionalExtendedDirichletGreen_exponentialKernelBound
    {m q : ℕ} [NeZero m] [NeZero q]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
      [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (K : GaugeZeroCochain 4 (m * (2 * q)) g →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) g)
    {A decay c : ℝ} (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (hK : FinitePiLpExponentialKernelBound K
      (finBoxDist : FinBox 4 (m * (2 * q)) →
        FinBox 4 (m * (2 * q)) → ℕ) A decay) :
    FinitePiLpExponentialKernelBound
      (cmp99RegionalExtendedDirichletGreen Omega K hc hKcoer)
      (finBoxDist : FinBox 4 (m * (2 * q)) →
        FinBox 4 (m * (2 * q)) → ℕ)
      (2 / c)
      (finitePiLpExponentialInverseDecayRate A decay
        (cmp99OmegaSiteExpSumBound (decay / 4)) c) := by
  let G := cmp99RegionalDirichletGreen Omega K hc hKcoer
  have hG := cmp99RegionalDirichletGreen_exponentialKernelBound
    Omega K hc hKcoer hK
  refine ⟨hG.1, hG.2.1, ?_⟩
  intro source target v
  by_cases hsource : source ∈ Omega.sites
  · by_cases htarget : target ∈ Omega.sites
    · let sourceOmega : ActiveGaugeRegion.Site Omega := ⟨source, hsource⟩
      let targetOmega : ActiveGaugeRegion.Site Omega := ⟨target, htarget⟩
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
      change ‖extendZeroZeroCLM Omega
          (G (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      rw [extendZeroZeroCLM_apply_of_mem Omega _ target htarget, hrestrict]
      change ‖G (singleFinitePiLp sourceOmega v) targetOmega‖ ≤ _
      exact hG.2.2 sourceOmega targetOmega v
    · change ‖extendZeroZeroCLM Omega
          (G (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      simp [extendZeroZeroCLM, htarget]
      exact mul_nonneg
        (mul_nonneg hG.1 (Real.exp_pos _).le) (norm_nonneg v)
  · have hrestrict : restrictZeroCLM Omega
        (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖extendZeroZeroCLM Omega
        (G (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
    rw [hrestrict]
    simp only [map_zero, PiLp.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg hG.1 (Real.exp_pos _).le) (norm_nonneg v)

/-- Exponential amplitude of the generated ambient precision at a chosen
positive rate. -/
noncomputable def cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude
    (M depth : ℕ) (spacing epsilon decay : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon *
    Real.exp (decay * (M ^ (depth + 1) : ℕ))

/-- The ambient reindexing of the generated physical precision retains its
literal finite-range exponential kernel estimate. -/
theorem cmp99SourceGeneratedPhysicalAmbientPrecision_exponentialKernelBound
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon decay : ℝ}
    (hspacing : 0 < spacing) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalAmbientPrecision
        (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
        (epsilon := epsilon) hM depth background budget fineSmall)
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude
        M depth spacing epsilon decay) decay := by
  let Omega := cmp99SourceGeneratedPhysicalFullCoarseRegion M Q
  let K := cmp99SourceGeneratedPhysicalPrecision
    (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
    (by norm_num) hM Omega depth spacing epsilon background budget fineSmall
  have hactive : FinitePiLpExponentialKernelBound K
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude
        M depth spacing epsilon decay) decay := by
    apply finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := cmp99SourceGeneratedPhysicalPrecisionUpperBound
        4 M (depth + 1) spacing epsilon)
      (R := M ^ (depth + 1))
    · exact (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
        4 M (depth + 1) (epsilon := epsilon) hspacing).le
    · exact hdecay
    · exact cmp99SourceGeneratedPhysicalPrecision_finiteRange
        (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
        (by norm_num) hM Omega depth spacing epsilon background budget fineSmall
    · exact cmp99SourceGeneratedPhysicalPrecision_kernelBound
        (d := 4) (M := M) (N := 2 * (M * Q)) (Nc := Nc)
        (by norm_num) hM Omega depth hspacing background budget fineSmall
  let e := cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex e e K
    (fun target source => finBoxDist target.1 source.1) hactive
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ) := by
    funext target source
    exact finBoxDist_cmp99SourceGeneratedPhysicalFullSiteEquiv_symm
      M Q depth target source
  rw [hdist] at hreindexed
  exact hreindexed

/-- Canonical Dirichlet region for one physical source large-block cell: the
literal support thickened by exactly the generated precision range. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalCell
    (P : CMP95SourceSmoothPartitionProfile) (M Q depth : ℕ)
    [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    ActiveGaugeRegion 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) :=
  cmp99RegionalFineSupportThickening
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P)
    (M ^ (depth + 1)) cell

/-- The physical regional cells have the exact collar against the generated
precision range, by construction rather than by a caller premise. -/
theorem cmp99SourceGeneratedPhysicalRegionalCell_hasFiniteRangeMargin
    (P : CMP95SourceSmoothPartitionProfile) (M Q depth : ℕ)
    [NeZero M] [NeZero Q] :
    CMP99RegionalSquarePartitionHasFiniteRangeMargin
      (cmp99SourceRegionalLargeBlockSquarePartition
        (M := M) (Q := Q) (depth := depth) P)
      (cmp99SourceGeneratedPhysicalRegionalCell P M Q depth)
      (M ^ (depth + 1)) :=
  cmp99RegionalFineSupportThickening_hasFiniteRangeMargin
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P)
    (M ^ (depth + 1))

/-- Canonical rate of every physical cell Dirichlet Green. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalGreenRate
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let decay := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let A := cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude
    M depth spacing epsilon decay
  let c := cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c

/-- Positivity of the canonical physical regional Green rate follows from
the one ambient Combes--Thomas rate and the generated coercivity budget. -/
theorem cmp99SourceGeneratedPhysicalRegionalGreenRate_pos
    (M depth : ℕ) [NeZero M] {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    0 < cmp99SourceGeneratedPhysicalRegionalGreenRate
      M depth spacing epsilon := by
  let decay := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  let A := cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude
    M depth spacing epsilon decay
  let S := cmp99OmegaSiteExpSumBound (decay / 4)
  let c := cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  have hdecay : 0 < decay :=
    cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
  have hA : 0 ≤ A := by
    dsimp [A, cmp99SourceGeneratedPhysicalAmbientPrecisionDecayAmplitude]
    exact mul_nonneg
      (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
        4 M (depth + 1) (epsilon := epsilon) hspacing).le
      (Real.exp_pos _).le
  have hS : 0 ≤ S := by
    dsimp [S, cmp99OmegaSiteExpSumBound]
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  change 0 < min (decay / 2) (c * decay / (8 * (A * S + 1)))
  exact lt_min (by positivity) (by positivity)

/-- Explicit amplitude of one physical regional correction before the final
source-overlap sum. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude
    (P : CMP95SourceSmoothPartitionProfile)
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let rate := cmp99SourceGeneratedPhysicalRegionalGreenRate
    M depth spacing epsilon
  let c := cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
      P M depth spacing epsilon rate *
    (2 / c) * cmp99OmegaSiteExpSumBound (rate / 2)

/-- The generated physical regional Green, extended back to the ambient
carrier, has a uniform cell-independent decay estimate. -/
theorem
    cmp99SourceGeneratedPhysicalRegionalExtendedGreen_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) (cell : FinBox 4 Q) :
    let K := cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
      (epsilon := epsilon) hM depth background budget fineSmall
    let c := cmp99SourceGeneratedCoercivity
      4 M (depth + 1) spacing epsilon
    FinitePiLpExponentialKernelBound
      (cmp99RegionalExtendedDirichletGreen
        (cmp99SourceGeneratedPhysicalRegionalCell P M Q depth cell)
        K (cmp99SourceGeneratedCoercivity_pos
          4 M depth hspacing hsmall)
        (isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
          (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
          background budget fineSmall hsmall))
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (2 / c)
      (cmp99SourceGeneratedPhysicalRegionalGreenRate
        M depth spacing epsilon) := by
  dsimp only
  let decay := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  have hdecay : 0 < decay :=
    cmp99SourceGeneratedCombesThomasRate_pos
      4 M depth hspacing hsmall
  have hK :=
    cmp99SourceGeneratedPhysicalAmbientPrecision_exponentialKernelBound
      (M := M) (Q := Q) (Nc := Nc) hM depth hspacing hdecay
      background budget fineSmall
  exact cmp99RegionalExtendedDirichletGreen_exponentialKernelBound
    (cmp99SourceGeneratedPhysicalRegionalCell P M Q depth cell)
    (cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
      (epsilon := epsilon) hM depth background budget fineSmall)
    (cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
      background budget fineSmall hsmall) hK

/-- The literal physical single-cell correction with all carrier, fibre and
source/target indices fixed in its public type.  This wrapper exposes no new
choice: its Green is still the canonical inverse of the compression of the
one generated ambient precision. -/
noncomputable def cmp99SourceGeneratedPhysicalRegionalCorrection
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) (cell : FinBox 4 Q) :
    GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
        (SUNLieCoord Nc) :=
  cmp99RegionalGreenCorrection
    (cmp99SourceRegionalLargeBlockSquarePartition
      (M := M) (Q := Q) (depth := depth) P)
    (cmp99SourceGeneratedPhysicalRegionalCell P M Q depth)
    (cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
      (epsilon := epsilon) hM depth background budget fineSmall)
    (cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
      background budget fineSmall hsmall)
    cell

/-- Step 6 of the declared route: a uniform exponential estimate for every
literal correction `K(h_Pi) G'_Pi h_Pi`.  The amplitude is independent of
the cell and periodic volume; the overlap factor `16` is deliberately not
paid here. -/
theorem cmp99SourceGeneratedPhysicalRegionalCorrection_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 ≤ M)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * (M * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) (cell : FinBox 4 Q) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalRegionalCorrection
        (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
        background budget fineSmall hsmall cell)
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude
        P M depth spacing epsilon)
      (cmp99SourceGeneratedPhysicalRegionalGreenRate
        M depth spacing epsilon / 2) := by
  let partition := cmp99SourceRegionalLargeBlockSquarePartition
    (M := M) (Q := Q) (depth := depth) P
  let regions := cmp99SourceGeneratedPhysicalRegionalCell P M Q depth
  let K := cmp99SourceGeneratedPhysicalAmbientPrecision
    (M := M) (Q := Q) (Nc := Nc) (spacing := spacing)
    (epsilon := epsilon) hM depth background budget fineSmall
  let c := cmp99SourceGeneratedCoercivity
    4 M (depth + 1) spacing epsilon
  let hc := cmp99SourceGeneratedCoercivity_pos
    4 M depth hspacing hsmall
  let hKcoer :=
    isCoerciveCLM_cmp99SourceGeneratedPhysicalAmbientPrecision
      (M := M) (Q := Q) (Nc := Nc) hM depth hspacing
      background budget fineSmall hsmall
  let rate := cmp99SourceGeneratedPhysicalRegionalGreenRate
    M depth spacing epsilon
  let S := cmp99OmegaSiteExpSumBound (rate / 2)
  have hrate : 0 < rate := by
    exact cmp99SourceGeneratedPhysicalRegionalGreenRate_pos
      M depth hspacing hsmall
  have hcomm : FinitePiLpExponentialKernelBound
      (cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc) partition cell K)
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate) rate := by
    exact
      cmp99SourceRegionalLargeBlockPrecisionCommutator_exponentialKernelBound
        (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing hrate
        background budget fineSmall cell
  have hgreen : FinitePiLpExponentialKernelBound
      (cmp99RegionalExtendedDirichletGreen (regions cell) K hc hKcoer)
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (2 / c) rate := by
    exact
      cmp99SourceGeneratedPhysicalRegionalExtendedGreen_exponentialKernelBound
        (M := M) (Q := Q) (Nc := Nc) P hM depth hspacing
        background budget fineSmall hsmall cell
  have hcomp : FinitePiLpExponentialKernelBound
      ((cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc) partition cell K).comp
          (cmp99RegionalExtendedDirichletGreen
            (regions cell) K hc hKcoer))
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
          P M depth spacing epsilon rate * (2 / c) * S)
      (rate - rate / 2) := by
    simpa [S] using finitePiLpExponentialKernelBound_comp_finBox
      (N := cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (g := SUNLieCoord Nc)
      (A := cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate)
      (B := 2 / c) (rate := rate) (sigma := rate / 2)
      (show 0 < rate / 2 by positivity) (by linarith)
      (cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc) partition cell K)
      (cmp99RegionalExtendedDirichletGreen
        (regions cell) K hc hKcoer) hcomm hgreen
  have hcut : FinitePiLpExponentialKernelBound
      (((cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc) partition cell K).comp
          (cmp99RegionalExtendedDirichletGreen
            (regions cell) K hc hKcoer)).comp
        (finitePiLpScalarMultiplier
          (g := SUNLieCoord Nc) (fun x => partition.value cell x)))
      (finBoxDist : FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) → ℕ)
      (cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
          P M depth spacing epsilon rate * (2 / c) * S)
      (rate - rate / 2) := by
    exact finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_right
      (ι := FinBox 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)))
      (κ := FinBox 4
        (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)))
      (g := SUNLieCoord Nc)
      (dist := finBoxDist)
      (A := cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
        P M depth spacing epsilon rate * (2 / c) * S)
      (rate := rate - rate / 2)
      (fun x => partition.value cell x)
      ((cmp99RegionalSquarePrecisionCommutator
        (M := cmp99SourceRegionalLargeBlockSide M depth)
        (Q := Q) (g := SUNLieCoord Nc) partition cell K).comp
          (cmp99RegionalExtendedDirichletGreen
            (regions cell) K hc hKcoer))
      (fun source => partition.norm_value_le_one cell source) hcomp
  have hrateEq : rate - rate / 2 = rate / 2 := by ring
  rw [hrateEq] at hcut
  simpa [cmp99RegionalGreenCorrection, cmp99RegionalSquareMultiplier,
    cmp99SourceGeneratedPhysicalRegionalCorrection,
    cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude,
    partition, regions, K, c, hc, hKcoer, rate, S,
    ContinuousLinearMap.comp_assoc] using hcut

end

end YangMills.RG
