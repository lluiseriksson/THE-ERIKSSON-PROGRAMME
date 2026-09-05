/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner
import YangMills.RG.BalabanCMP99SourceSeparatedSignedLargeBlockPartition

/-!
# Source-owner overlap for the CMP99 (3.89) cell sum

This module was compiler-verified at exact source checkpoint
`a814d95ac5bb20fa8bfe8871e8764caf2353153b` in cold GitHub Actions run
`31180210309`; its six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

CMP99 (3.89) is first proved for one regional cell and is then summed over
cells.  Pointwise overlap does not by itself control that sum on a complete
source-owner fibre.  This module derives the required common window directly
from the source geometry.

One source-localization block has side `L^(depth+1)`, whereas the signed
periodic cutoff has scale `2*K*L^(depth+1)`.  Thus every point of one owner
fibre is at normalized distance at most `1/(4*K) <= 1/4` from its midpoint.
The CMP95 support radius is `2/3`, so an active translate remains within
`2/3 + 1/4 = 11/12 < 1` of that midpoint.  There are consequently only two
residue classes in each coordinate and at most `2^4 = 16` cells in total.

No overlap bound and no estimate on delta probes is accepted from the caller.
-/

namespace YangMills.RG

noncomputable section

variable {L K Q depth : ℕ} [NeZero L] [NeZero K] [NeZero Q]

/-- Moving the observation point by at most `1/4` cannot enlarge the two-class
window forced by the CMP95 support radius `2/3`. -/
theorem mem_cmp95PeriodicActiveCellWindow_of_squareWeight_ne_zero_of_abs_sub_le_quarter
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (x y : ℝ)
    (hweight : cmp95PeriodicSquareWeight P Q cell x ≠ 0)
    (hxy : |x - y| ≤ 1 / 4) :
    cell ∈ cmp95PeriodicActiveCellWindow Q y := by
  classical
  have hexists : ∃ k : ℤ,
      P.value
        (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hweight
    unfold cmp95PeriodicSquareWeight
    calc
      (∑' k : ℤ,
          P.value
            (x - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2) =
          ∑' _k : ℤ, 0 := tsum_congr hnone
      _ = 0 := tsum_zero
  obtain ⟨k, hk⟩ := hexists
  let n : ℤ := k * (Q : ℤ) + (cell.val : ℤ)
  have hvalue : P.value (x - (n : ℝ)) ≠ 0 := by
    intro hz
    apply hk
    push_cast [n] at hz ⊢
    rw [hz]
    norm_num
  have hsupp : x - (n : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (2 / 3) :=
    P.support_subset (Function.mem_support.mpr hvalue)
  have hfloorLower : (((⌊y⌋ : ℤ) : ℝ)) ≤ y := Int.floor_le y
  have hfloorUpper : y < (((⌊y⌋ : ℤ) : ℝ)) + 1 := Int.lt_floor_add_one y
  have hxyBounds : -(1 / 4 : ℝ) ≤ x - y ∧ x - y ≤ 1 / 4 :=
    (abs_le.mp hxy)
  have hnLowerReal : ((((⌊y⌋ : ℤ) - 1 : ℤ)) : ℝ) < (n : ℝ) := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    push_cast
    nlinarith
  have hnUpperReal : (n : ℝ) < (((⌊y⌋ : ℤ) + 2 : ℤ) : ℝ) := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    push_cast
    nlinarith
  have hnLower : (⌊y⌋ : ℤ) ≤ n := by
    have : (⌊y⌋ : ℤ) - 1 < n := by exact_mod_cast hnLowerReal
    omega
  have hnUpper : n ≤ (⌊y⌋ : ℤ) + 1 := by
    have : n < (⌊y⌋ : ℤ) + 2 := by exact_mod_cast hnUpperReal
    omega
  have hnWindow : n ∈ Finset.Icc ⌊y⌋ (⌊y⌋ + 1) :=
    Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩
  have hnSymm :
      n = (Int.divModEquiv Q).symm (k, cell) := by
    simp [n, Int.divModEquiv_symm_apply]
  have hpair : (Int.divModEquiv Q) n = (k, cell) := by
    rw [hnSymm, Equiv.apply_symm_apply]
  have hresidue : cmp95PeriodicTranslateResidue Q n = cell := by
    exact congrArg Prod.snd hpair
  exact Finset.mem_image.mpr ⟨n, hnWindow, hresidue⟩

/-- Midpoint of one source-localization owner fibre in the dimensionless
coordinate used by the physically rescaled periodic cutoff. -/
def cmp99Eq389SourceOwnerNormalizedCenter
    (L K depth : ℕ) (owner : FinBox 4 (2 * (K * Q))) : Fin 4 → ℝ :=
  fun i =>
    (((L ^ (depth + 1) : ℝ) * (owner i).val +
          (L ^ (depth + 1) : ℝ) / 2 -
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) / 2) /
      (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ))

/-- Every fine site lies within normalized distance `1/4` of the midpoint of
its literal source-localization owner fibre. -/
theorem abs_cmp99SourceSeparatedLargeBlockCoordinate_div_sub_ownerCenter_le_quarter
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (i : Fin 4) :
    |cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun j => (x j).val) i /
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ) -
        cmp99Eq389SourceOwnerNormalizedCenter (Q := Q) L K depth
          (cmp99Eq389SourceLocalizationOwner L K Q depth x) i| ≤ 1 / 4 := by
  let ell : ℕ := L ^ (depth + 1)
  let M0 : ℕ := cmp99SourceSeparatedLargeBlockCutoffScale L K depth
  let x' := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth x
  let owner := cmp99Eq389SourceLocalizationOwner L K Q depth x
  have howner : blockSite ell (2 * (K * Q)) x' = owner := by
    rfl
  have hcube := (blockSite_eq_iff_cube ell (2 * (K * Q)) x' owner).mp howner
  have hxval : (x' i).val = (x i).val := by
    unfold x' cmp99Eq389SourceLocalizationSiteEquiv
    let hcarrier :=
      cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth
    have equivCastFinBoxVal {n m : ℕ} (h : n = m) (y : FinBox 4 n)
        (j : Fin 4) :
        ((Equiv.cast (congrArg (FinBox 4) h) y) j).val = (y j).val := by
      subst h
      rfl
    exact equivCastFinBoxVal hcarrier x i
  have hxLowerNat : ell * (owner i).val ≤ (x i).val := by
    rw [← hxval]
    exact (hcube i).1
  have hxUpperNat : (x i).val + 1 ≤ ell * (owner i).val + ell := by
    have hxUpperNat' : (x' i).val + 1 ≤ ell * (owner i).val + ell :=
      Nat.succ_le_of_lt (hcube i).2
    simpa only [hxval] using hxUpperNat'
  have hxLower : (ell : ℝ) * (owner i).val ≤ ((x i).val : ℝ) := by
    exact_mod_cast hxLowerNat
  have hxUpper : ((x i).val : ℝ) + 1 ≤
      (ell : ℝ) * (owner i).val + ell := by
    exact_mod_cast hxUpperNat
  have hell : 1 ≤ (ell : ℝ) := by
    have hellNat : 1 ≤ ell := by
      apply Nat.one_le_iff_ne_zero.mpr
      exact pow_ne_zero _ (NeZero.ne L)
    exact_mod_cast hellNat
  have hK : 1 ≤ (K : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne K))
  have hM0pos : 0 < (M0 : ℝ) := by
    exact_mod_cast cmp99SourceSeparatedLargeBlockCutoffScale_pos L K depth
  have hM0 : (M0 : ℝ) = 2 * (K : ℝ) * (ell : ℝ) := by
    unfold M0 ell cmp99SourceSeparatedLargeBlockCutoffScale
      cmp99SourceSeparatedLargeBlockSide
    push_cast
    ring
  have hdiff :
      cmp99SourceSeparatedLargeBlockCoordinate L K depth
            (fun j => (x j).val) i / (M0 : ℝ) -
          cmp99Eq389SourceOwnerNormalizedCenter (Q := Q) L K depth owner i =
        (((x i).val : ℝ) + 1 / 2 -
          (ell : ℝ) * (owner i).val - (ell : ℝ) / 2) / (M0 : ℝ) := by
    unfold cmp99SourceSeparatedLargeBlockCoordinate
      cmp99Eq389SourceOwnerNormalizedCenter M0 ell
      cmp99SourceSeparatedLargeBlockCutoffScale
      cmp99SourceSeparatedLargeBlockSide
    push_cast
    ring
  change |cmp99SourceSeparatedLargeBlockCoordinate L K depth
          (fun j => (x j).val) i / (M0 : ℝ) -
        cmp99Eq389SourceOwnerNormalizedCenter (Q := Q) L K depth owner i| ≤ 1 / 4
  rw [hdiff, abs_le]
  constructor
  · rw [le_div_iff₀ hM0pos]
    nlinarith [hM0]
  · rw [div_le_iff₀ hM0pos]
    nlinarith [hM0]

/-- The common sixteen-cell window attached to one source-localization owner,
rather than to one individual fine site. -/
def cmp99Eq389SourceOwnerActiveCellWindow
    (L K Q depth : ℕ) [NeZero Q]
    (owner : FinBox 4 (2 * (K * Q))) : Finset (FinBox 4 Q) :=
  cmp95PeriodicTensorActiveCellWindow Q
    (cmp99Eq389SourceOwnerNormalizedCenter (Q := Q) L K depth owner)

/-- The common owner window has the literal source overlap `2^4 = 16`. -/
theorem card_cmp99Eq389SourceOwnerActiveCellWindow_le_sixteen
    (L K Q depth : ℕ) [NeZero Q]
    (owner : FinBox 4 (2 * (K * Q))) :
    (cmp99Eq389SourceOwnerActiveCellWindow L K Q depth owner).card ≤ 16 := by
  exact card_cmp95PeriodicTensorActiveCellWindow_le_sixteen Q _

/-- A signed cutoff active at a fine site belongs to the one common window of
that site's complete source-owner fibre. -/
theorem mem_cmp99Eq389SourceOwnerActiveCellWindow_of_signedCutoff_ne_zero
    (P : CMP95SourceSmoothPartitionProfile)
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    (cell : FinBox 4 Q)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (hcutoff :
      cmp99SourceSeparatedSignedLargeBlockCutoff P L K Q depth cell x ≠ 0) :
    cell ∈ cmp99Eq389SourceOwnerActiveCellWindow L K Q depth
      (cmp99Eq389SourceLocalizationOwner L K Q depth x) := by
  classical
  have hweight :
      cmp95RescaledPeriodicTensorSquareWeight P Q
          (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
          (cmp99SourceSeparatedLargeBlockCoordinate L K depth
            fun i => (x i).val) ≠ 0 := by
    have hraw :
        cmp95RescaledSourcePeriodicSignedTensorCutoff P Q
            (cmp99SourceSeparatedLargeBlockCutoffScale L K depth) cell
            (cmp99SourceSeparatedLargeBlockCoordinate L K depth
              fun i => (x i).val) ≠ 0 := by
      simpa [cmp99SourceSeparatedSignedLargeBlockCutoff] using hcutoff
    rw [← cmp95RescaledSourcePeriodicSignedTensorCutoff_sq]
    exact pow_ne_zero 2 hraw
  rw [cmp99Eq389SourceOwnerActiveCellWindow,
    cmp95PeriodicTensorActiveCellWindow, Fintype.mem_piFinset]
  intro i
  apply
    mem_cmp95PeriodicActiveCellWindow_of_squareWeight_ne_zero_of_abs_sub_le_quarter
      P Q (cell i)
      (cmp99SourceSeparatedLargeBlockCoordinate L K depth
        (fun j => (x j).val) i /
        (cmp99SourceSeparatedLargeBlockCutoffScale L K depth : ℝ))
      (cmp99Eq389SourceOwnerNormalizedCenter (Q := Q) L K depth
        (cmp99Eq389SourceLocalizationOwner L K Q depth x) i)
  · intro hcoord
    apply hweight
    unfold cmp95RescaledPeriodicTensorSquareWeight
      cmp95RescaledPeriodicSquareWeight
    exact Finset.prod_eq_zero (Finset.mem_univ i) hcoord
  · exact
      abs_cmp99SourceSeparatedLargeBlockCoordinate_div_sub_ownerCenter_le_quarter
        L K Q depth x i

end

end YangMills.RG
