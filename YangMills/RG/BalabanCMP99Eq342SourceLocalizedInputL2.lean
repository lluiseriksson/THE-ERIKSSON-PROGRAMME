/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate

/-!
# PRE-VALIDATION: source-localized input L2 scale for CMP99 (3.42)

The source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

CMP99 (3.42) tests the regional Green on an arbitrary field supported in one
localization block of side `ell = L^(depth+1)`.  Before any Green estimate is
used, the counting-L2 norm of such an input costs exactly the square root of
the source-fibre cardinality.  In dimension four that is at most `ell^2`,
which is the first entry of the printed scale vector `[ell^2, ell, ell, 1]`.

This module proves only that input-size conversion.  It does not derive a
localized Green estimate, choose the constants `B0` or `delta0`, prove their
uniformity in the regional parameter `K`, or attain the Eq. (3.89)
contraction window.
-/

namespace YangMills.RG

noncomputable section

/-- A counting-L2 field supported in one owner fibre pays only the square
root of that fibre's cardinality when compared with the finite supremum
norm.  The ambient cardinality does not occur. -/
theorem norm_finitePiLp_le_sqrt_ownerFiber_card_mul_supNorm
    {ι β g : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq β]
    [NormedAddCommGroup g]
    (sourceOwner : ι → β) (owner : β) (f : FinitePiLpField ι g)
    (hf : FinitePiLpSupportedInOwner sourceOwner owner f) :
    ‖f‖ ≤
      Real.sqrt ((Finset.univ.filter
        (fun i => sourceOwner i = owner)).card : ℝ) * finitePiLpSupNorm f := by
  classical
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (finitePiLpSupNorm_nonneg f), ?_⟩
  calc
    (∑ i : ι, ‖f i‖ ^ 2) =
        ∑ i ∈ Finset.univ.filter (fun i => sourceOwner i = owner),
          ‖f i‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _hi hinot
      have hne : sourceOwner i ≠ owner := by
        simpa using hinot
      rw [hf i hne, norm_zero, zero_pow]
      norm_num
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => sourceOwner i = owner),
          finitePiLpSupNorm f ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ (norm_nonneg (f i))
        (norm_apply_le_finitePiLpSupNorm f i) 2
    _ = ((Finset.univ.filter
          (fun i => sourceOwner i = owner)).card : ℝ) *
        finitePiLpSupNorm f ^ 2 := by
      simp
    _ = (Real.sqrt ((Finset.univ.filter
          (fun i => sourceOwner i = owner)).card : ℝ) *
        finitePiLpSupNorm f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

variable {L K Q Nc : ℕ} [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private instance instNeZeroEq342InputL2BlockSide
    (L depth : ℕ) [NeZero L] : NeZero (L ^ (depth + 1)) :=
  ⟨(pow_pos (NeZero.pos L) (depth + 1)).ne'⟩

private instance instNeZeroEq342InputL2CoarseSide
    (K Q : ℕ) [NeZero K] [NeZero Q] : NeZero (2 * (K * Q)) :=
  ⟨(Nat.mul_pos (by omega)
    (Nat.mul_pos (NeZero.pos K) (NeZero.pos Q))).ne'⟩

/-- An active source-localization fibre injects into the complete ambient
`L^(depth+1)` block with the same owner.  Hence its cardinality is at most
`L^(4*(depth+1))`; deleting sites from the active region cannot enlarge it. -/
theorem card_cmp99Eq342SourceLocalizedActiveOwner_fiber_le
    (depth : ℕ)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (owner : FinBox 4 (2 * (K * Q))) :
    (Finset.univ.filter (fun x : ActiveGaugeRegion.Site Omega =>
      cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner)).card ≤
        (L ^ (depth + 1)) ^ 4 := by
  classical
  let siteEquiv := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth
  let sourceFiber := Finset.univ.filter
    (fun x : ActiveGaugeRegion.Site Omega =>
      cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner)
  let ambientBlock := blockOf (L ^ (depth + 1)) (2 * (K * Q)) owner
  have hmaps : ∀ x ∈ sourceFiber, siteEquiv x.1 ∈ ambientBlock := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [mem_blockOf]
    simpa [cmp99Eq342SourceLocalizedActiveOwner,
      cmp99Eq389SourceLocalizationOwner, siteEquiv] using hx.2
  have hinj : Set.InjOn (fun x : ActiveGaugeRegion.Site Omega =>
      siteEquiv x.1) sourceFiber := by
    intro x _hx y _hy hxy
    apply Subtype.ext
    exact siteEquiv.injective hxy
  have hcard : sourceFiber.card ≤ ambientBlock.card :=
    Finset.card_le_card_of_injOn (fun x : ActiveGaugeRegion.Site Omega =>
      siteEquiv x.1) hmaps hinj
  simpa [sourceFiber, ambientBlock, blockOf_card] using hcard

/-- Exact four-dimensional source-input scale consumed by the value part of
CMP99 (3.42): support in one source-localization owner gives the factor
`L^(2*(depth+1))`, with no ambient-volume or regional-`K` factor. -/
theorem norm_finitePiLp_le_cmp99Eq342_sourceScale_mul_supNorm
    (depth : ℕ)
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (owner : FinBox 4 (2 * (K * Q)))
    (f : FinitePiLpField (ActiveGaugeRegion.Site Omega) (SUNLieCoord Nc))
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner f) :
    ‖f‖ ≤ (L ^ (depth + 1) : ℝ) ^ 2 * finitePiLpSupNorm f := by
  have hbase := norm_finitePiLp_le_sqrt_ownerFiber_card_mul_supNorm
    (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner f hf
  have hcard := card_cmp99Eq342SourceLocalizedActiveOwner_fiber_le
    (L := L) (K := K) (Q := Q) depth Omega owner
  have hsqrt :
      Real.sqrt ((Finset.univ.filter
        (fun x : ActiveGaugeRegion.Site Omega =>
          cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner)).card : ℝ) ≤
        (L ^ (depth + 1) : ℝ) ^ 2 := by
    calc
      Real.sqrt ((Finset.univ.filter
          (fun x : ActiveGaugeRegion.Site Omega =>
            cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner)).card : ℝ) ≤
          Real.sqrt (((L ^ (depth + 1)) ^ 4 : ℕ) : ℝ) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hcard)
      _ = (L ^ (depth + 1) : ℝ) ^ 2 := by
        push_cast
        change Real.sqrt (((L : ℝ) ^ (depth + 1)) ^ 4) =
          ((L : ℝ) ^ (depth + 1)) ^ 2
        rw [show ((L : ℝ) ^ (depth + 1)) ^ 4 =
          (((L : ℝ) ^ (depth + 1)) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (sq_nonneg _)]
  calc
    ‖f‖ ≤ Real.sqrt ((Finset.univ.filter
          (fun x : ActiveGaugeRegion.Site Omega =>
            cmp99Eq342SourceLocalizedActiveOwner L K Q depth x = owner)).card : ℝ) *
        finitePiLpSupNorm f := hbase
    _ ≤ (L ^ (depth + 1) : ℝ) ^ 2 * finitePiLpSupNorm f :=
      mul_le_mul_of_nonneg_right hsqrt (finitePiLpSupNorm_nonneg f)

end

end YangMills.RG
