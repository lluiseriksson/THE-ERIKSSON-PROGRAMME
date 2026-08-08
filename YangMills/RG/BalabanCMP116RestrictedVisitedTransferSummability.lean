/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers
import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm

/-!
# Summability of the restricted visited-state transfer powers

The finite transfer matrix has only the declared physical successors in each
row.  A transition charges at most the active-carrier budget and carries one
continuation factor.  Consequently its block `L∞` operator norm is bounded by

`K * rho * Rweak ^ B`.

This gives summability of the transfer powers under the same local branching
condition as the physical walk series.  The state-space cardinality, including
the visited powerset, never occurs.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

universe u v w

/-- Local branching, active support, and continuation bounds control the
complete visited-state transfer matrix without its ambient state count. -/
theorem norm_cmp116RestrictedVisitedTransferMatrix_le
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain] [Nonempty Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (K B : ℕ) (rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hrho : 0 ≤ rho) (hRweak : 1 ≤ Rweak)
    (hR : ∀ label domain, ‖R label domain‖ ≤ rho)
    (hsigma : ∀ d ∈ carrier, ‖sigma d‖ ≤ Rweak) :
    ‖cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma‖ ≤
      (K : ℝ) * rho * Rweak ^ B := by
  classical
  let transfer :=
    cmp116RestrictedVisitedTransferMatrix
      carrier domainActive successors R sigma
  have hRweak0 : 0 ≤ Rweak := le_trans (by norm_num) hRweak
  have hweight :
      ∀ (visited : CMP116RestrictedVisitedState carrier) domain,
        ‖CMP116RestrictedVisitedState.transitionWeight
            carrier sigma visited (domainActive domain)‖ ≤ Rweak ^ B := by
    intro visited domain
    let newly :=
      CMP116RestrictedVisitedState.newlyActive carrier visited
        (domainActive domain)
    have hnewCarrier : newly ⊆ carrier :=
      CMP116RestrictedVisitedState.newlyActive_subset carrier visited
        (domainActive domain)
    have hnewActive : newly ⊆ domainActive domain :=
      Finset.sdiff_subset.trans Finset.inter_subset_left
    have hcard : newly.card ≤ B :=
      (Finset.card_le_card hnewActive).trans (hB domain)
    have hmono :
        ‖cmp116ComplexWeakeningMonomial newly sigma‖ ≤
          Rweak ^ newly.card := by
      apply norm_cmp116ComplexWeakeningMonomial_le_pow_card
        newly sigma (fun _ => Rweak - 1) Rweak hRweak0
      · intro d hd
        have hdCarrier := hnewCarrier hd
        convert hsigma d hdCarrier using 1
        ring
      · intro d hd
        convert le_rfl using 1
        ring
    exact hmono.trans (pow_le_pow_right₀ hRweak hcard)
  have hentry :
      ∀ source target,
        ‖transfer source target‖ ≤ Rweak ^ B * rho := by
    intro source target
    rcases target with ⟨⟨kind, targetDomain⟩, targetVisited⟩
    cases kind with
    | none =>
        rw [show transfer source
            (⟨⟨none, targetDomain⟩, targetVisited⟩ :
              CMP116RestrictedTransferState Label Domain carrier) = 0 by
          simp [transfer, cmp116RestrictedVisitedTransferMatrix]]
        rw [norm_zero]
        exact mul_nonneg (pow_nonneg hRweak0 _) hrho
    | some label =>
        simp only [transfer, cmp116RestrictedVisitedTransferMatrix]
        split
        next hstep =>
          split
          next hstate =>
            rw [norm_smul]
            exact mul_le_mul
              (hweight source.2 targetDomain)
              (hR label targetDomain) (norm_nonneg _)
              (pow_nonneg hRweak0 _)
          next hstate =>
            simp [mul_nonneg (pow_nonneg hRweak0 _) hrho]
        next hstep =>
          simp [mul_nonneg (pow_nonneg hRweak0 _) hrho]
  let state0 : CMP116RestrictedTransferState Label Domain carrier :=
    (⟨none, Classical.arbitrary Domain⟩,
      CMP116RestrictedVisitedState.empty carrier)
  letI : Nonempty
      (CMP116RestrictedTransferState Label Domain carrier) := ⟨state0⟩
  apply Matrix.linfty_opNorm_le_of_row_sum_le
  · positivity
  · intro source
    let generated :=
      (successors source.1.domain).image
        (cmp116RestrictedTransferNextState
          carrier domainActive source.2)
    calc
      ∑ target, ‖transfer source target‖ =
          ∑ target ∈ generated, ‖transfer source target‖ := by
        symm
        apply Finset.sum_subset (Finset.subset_univ generated)
        intro target _ hnot
        change
          ‖cmp116RestrictedVisitedTransferMatrix
              carrier domainActive successors R sigma source target‖ = 0
        rw [cmp116RestrictedVisitedTransferMatrix_apply_eq_zero_of_not_mem_nextStates
          carrier domainActive successors R sigma source target hnot]
        simp
      _ ≤ ∑ _target ∈ generated, (Rweak ^ B * rho) := by
        exact Finset.sum_le_sum fun target _ => hentry source target
      _ = (generated.card : ℝ) * (Rweak ^ B * rho) := by simp
      _ ≤ (K : ℝ) * (Rweak ^ B * rho) := by
        gcongr
        exact Finset.card_image_le.trans (hK source.1.domain)
      _ = (K : ℝ) * rho * Rweak ^ B := by ring

/-- The physical local ratio below one produces the Neumann summability
needed by the finite visited-state resolvent. -/
theorem summable_cmp116RestrictedVisitedTransferMatrix_pow
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain] [Nonempty Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (K B : ℕ) (rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hrho : 0 ≤ rho) (hRweak : 1 ≤ Rweak)
    (hR : ∀ label domain, ‖R label domain‖ ≤ rho)
    (hsigma : ∀ d ∈ carrier, ‖sigma d‖ ≤ Rweak)
    (hsmall : (K : ℝ) * rho * Rweak ^ B < 1) :
    Summable fun n : ℕ =>
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma ^ n := by
  apply summable_geometric_of_norm_lt_one
  exact lt_of_le_of_lt
    (norm_cmp116RestrictedVisitedTransferMatrix_le
      carrier domainActive successors R sigma K B rho Rweak
      hK hB hrho hRweak hR hsigma)
    hsmall

end

end YangMills.RG
