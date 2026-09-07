/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237

/-!
# The CMP116 equation-(2.34) gap-subset sum

After reserving half of the outer Cauchy decay, CMP116 sums over the possible
gap variables `Z \ Z0'`.  For a carrier with `n` independent coordinates the
literal weight is

`exp (-((kappa1 - 1) / 2) * |Q|)`.

The sum over all subsets is exactly

`(1 + exp (-((kappa1 - 1) / 2))) ^ n`

and is bounded by the equation-(2.34) exponential

`exp (exp (-((kappa1 - 1) / 2)) * n)`.

This module proves that finite combinatorial step and its physical
normalization `n = (LM)^(-4) |Z|`.  It does not identify the source carrier;
that remains a geometric dictionary theorem.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Reserved outer-Cauchy weight for one gap subset. -/
def cmp116Eq234GapSubsetWeight
    {α : Type*} (kappa1 : ℝ) (Q : Finset α) : ℝ :=
  Real.exp (-(((kappa1 - 1) / 2) * (Q.card : ℝ)))

/-- Source dictionary identifying each physical `Z0'` choice with its gap
subset of a common finite carrier.  Injectivity is required only on the
physical index; the image may be smaller than the full powerset, which is
precisely the harmless overcount used in equation (2.34). -/
structure CMP116Eq234GapIndexEncoding
    {ιZ0' : Type*} (α : Type*)
    (index : Finset ιZ0')
    (gapCard : ιZ0' → ℕ)
    (localizationScale : ℕ) where
  carrier : Finset α
  gapOf : ιZ0' → Finset α
  gap_subset :
    ∀ Z0', Z0' ∈ index → gapOf Z0' ⊆ carrier
  gap_injective : Set.InjOn gapOf index
  normalized_gap :
    ∀ Z0', Z0' ∈ index →
      ((((localizationScale : ℝ) ^ 4)⁻¹) *
        (gapCard Z0' : ℝ)) =
          ((gapOf Z0').card : ℝ)

/-- The gap-subset sum is the literal finite binomial. -/
theorem cmp116Eq234_gapSubsetSum_eq
    {α : Type*} [DecidableEq α]
    (carrier : Finset α) (kappa1 : ℝ) :
    (∑ Q ∈ carrier.powerset,
        cmp116Eq234GapSubsetWeight kappa1 Q) =
      (1 + Real.exp (-((kappa1 - 1) / 2))) ^ carrier.card := by
  let q : ℝ := Real.exp (-((kappa1 - 1) / 2))
  have hweight :
      ∀ Q : Finset α,
        cmp116Eq234GapSubsetWeight kappa1 Q = q ^ Q.card := by
    intro Q
    unfold cmp116Eq234GapSubsetWeight
    dsimp [q]
    rw [show
        -(((kappa1 - 1) / 2) * (Q.card : ℝ)) =
          (Q.card : ℝ) * (-((kappa1 - 1) / 2)) by ring,
      Real.exp_nat_mul]
  calc
    (∑ Q ∈ carrier.powerset,
        cmp116Eq234GapSubsetWeight kappa1 Q) =
      ∑ Q ∈ carrier.powerset, q ^ Q.card := by
        exact Finset.sum_congr rfl fun Q _ => hweight Q
    _ =
      ∑ Q ∈ carrier.powerset,
        ∏ _x ∈ Q, q := by
          exact Finset.sum_congr rfl fun Q _ => by
            rw [Finset.prod_const]
    _ = ∏ _x ∈ carrier, (1 + q) := by
      exact
        (Finset.prod_one_add
          (s := carrier) (f := fun _ : α => q)).symm
    _ = (1 + q) ^ carrier.card := by rw [Finset.prod_const]
    _ =
      (1 + Real.exp (-((kappa1 - 1) / 2))) ^ carrier.card := rfl

/-- Equation (2.34): the exact binomial is bounded by its exponential
majorant. -/
theorem cmp116Eq234_gapSubsetSum_le_exp
    {α : Type*} [DecidableEq α]
    (carrier : Finset α) (kappa1 : ℝ) :
    (∑ Q ∈ carrier.powerset,
        cmp116Eq234GapSubsetWeight kappa1 Q) ≤
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          (carrier.card : ℝ)) := by
  rw [cmp116Eq234_gapSubsetSum_eq]
  let q : ℝ := Real.exp (-((kappa1 - 1) / 2))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hbase : 1 + q ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    linarith
  calc
    (1 + Real.exp (-((kappa1 - 1) / 2))) ^ carrier.card =
      (1 + q) ^ carrier.card := rfl
    _ ≤ (Real.exp q) ^ carrier.card := by
      exact pow_le_pow_left₀ (add_nonneg zero_le_one hq) hbase _
    _ = Real.exp ((carrier.card : ℝ) * q) := by
      exact (Real.exp_nat_mul q carrier.card).symm
    _ =
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          (carrier.card : ℝ)) := by
            congr 1
            dsimp [q]
            ring

/-- A physical gap-index encoding reduces the source sum over `Z0'` to the
equation-(2.34) powerset bound. -/
theorem cmp116Eq234_gapIndexSum_le_exp
    {ιZ0' α : Type*} [DecidableEq ιZ0'] [DecidableEq α]
    (index : Finset ιZ0')
    (gapCard : ιZ0' → ℕ)
    (localizationScale : ℕ)
    (E :
      CMP116Eq234GapIndexEncoding
        α index gapCard localizationScale)
    (kappa1 : ℝ) :
    (∑ Z0' ∈ index,
        Real.exp
          (-(((kappa1 - 1) / 2) *
            (((localizationScale : ℝ) ^ 4)⁻¹) *
            (gapCard Z0' : ℝ)))) ≤
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          (E.carrier.card : ℝ)) := by
  have hweight :
      ∀ Z0', Z0' ∈ index →
        Real.exp
            (-(((kappa1 - 1) / 2) *
              (((localizationScale : ℝ) ^ 4)⁻¹) *
              (gapCard Z0' : ℝ))) =
          cmp116Eq234GapSubsetWeight kappa1 (E.gapOf Z0') := by
    intro Z0' hZ0'
    unfold cmp116Eq234GapSubsetWeight
    congr 1
    calc
      -(((kappa1 - 1) / 2) *
          (((localizationScale : ℝ) ^ 4)⁻¹) *
          (gapCard Z0' : ℝ)) =
        -(((kappa1 - 1) / 2) *
          ((((localizationScale : ℝ) ^ 4)⁻¹) *
            (gapCard Z0' : ℝ))) := by ring
      _ =
        -(((kappa1 - 1) / 2) *
          ((E.gapOf Z0').card : ℝ)) := by
            rw [E.normalized_gap Z0' hZ0']
  have hsum_image :
      (∑ Z0' ∈ index,
          cmp116Eq234GapSubsetWeight kappa1 (E.gapOf Z0')) =
        ∑ Q ∈ index.image E.gapOf,
          cmp116Eq234GapSubsetWeight kappa1 Q := by
    simpa using
      (Finset.sum_image
        (s := index)
        (g := E.gapOf)
        (f := cmp116Eq234GapSubsetWeight kappa1)
        E.gap_injective).symm
  have himage :
      index.image E.gapOf ⊆ E.carrier.powerset := by
    intro Q hQ
    rw [Finset.mem_image] at hQ
    obtain ⟨Z0', hZ0', rfl⟩ := hQ
    exact Finset.mem_powerset.mpr (E.gap_subset Z0' hZ0')
  calc
    (∑ Z0' ∈ index,
        Real.exp
          (-(((kappa1 - 1) / 2) *
            (((localizationScale : ℝ) ^ 4)⁻¹) *
            (gapCard Z0' : ℝ)))) =
      ∑ Z0' ∈ index,
        cmp116Eq234GapSubsetWeight kappa1 (E.gapOf Z0') := by
          exact Finset.sum_congr rfl hweight
    _ =
      ∑ Q ∈ index.image E.gapOf,
        cmp116Eq234GapSubsetWeight kappa1 Q := hsum_image
    _ ≤
      ∑ Q ∈ E.carrier.powerset,
        cmp116Eq234GapSubsetWeight kappa1 Q := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            himage
            (fun Q _ _ => (Real.exp_pos _).le)
    _ ≤
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          (E.carrier.card : ℝ)) :=
            cmp116Eq234_gapSubsetSum_le_exp E.carrier kappa1

/-- The encoded gap sum in the physical volume normalization of equation
(2.34). -/
theorem cmp116Eq234_gapIndexSum_le_exp_sourceCard
    {ιZ0' α : Type*} [DecidableEq ιZ0'] [DecidableEq α]
    (index : Finset ιZ0')
    (gapCard : ιZ0' → ℕ)
    (localizationScale blockScale sourceCard : ℕ)
    (E :
      CMP116Eq234GapIndexEncoding
        α index gapCard localizationScale)
    (hcarrier :
      (E.carrier.card : ℝ) =
        ((((localizationScale * blockScale : ℕ) : ℝ) ^ 4)⁻¹) *
          (sourceCard : ℝ))
    (kappa1 : ℝ) :
    (∑ Z0' ∈ index,
        Real.exp
          (-(((kappa1 - 1) / 2) *
            (((localizationScale : ℝ) ^ 4)⁻¹) *
            (gapCard Z0' : ℝ)))) ≤
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          ((((localizationScale * blockScale : ℕ) : ℝ) ^ 4)⁻¹) *
          (sourceCard : ℝ)) := by
  have h :=
    cmp116Eq234_gapIndexSum_le_exp
      index gapCard localizationScale E kappa1
  rw [hcarrier] at h
  simpa [mul_assoc] using h

/-- Source-normalized equation-(2.34) bound when the number of independent
gap coordinates is `(LM)^(-4) |Z|`. -/
theorem cmp116Eq234_gapSubsetSum_le_exp_sourceCard
    {α : Type*} [DecidableEq α]
    (carrier : Finset α) (kappa1 : ℝ)
    (localizationScale blockScale sourceCard : ℕ)
    (hnormalized :
      (carrier.card : ℝ) =
        (((localizationScale * blockScale : ℕ) : ℝ) ^ 4)⁻¹ *
          (sourceCard : ℝ)) :
    (∑ Q ∈ carrier.powerset,
        cmp116Eq234GapSubsetWeight kappa1 Q) ≤
      Real.exp
        (Real.exp (-((kappa1 - 1) / 2)) *
          (((localizationScale * blockScale : ℕ) : ℝ) ^ 4)⁻¹ *
          (sourceCard : ℝ)) := by
  have h := cmp116Eq234_gapSubsetSum_le_exp carrier kappa1
  rw [hnormalized] at h
  simpa [mul_assoc] using h

end

end YangMills.RG
