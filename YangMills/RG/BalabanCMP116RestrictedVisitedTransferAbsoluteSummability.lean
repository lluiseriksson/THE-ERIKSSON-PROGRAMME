/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferEntry
import YangMills.RG.BalabanCMP116Eq214ContourRelativeNorm

/-!
# Absolute physical-tail criterion for restricted transfer powers

The entrywise tail expansion lets a whole-tail estimate control each transfer
power without multiplying norms of coordinate matrices factor by factor.
Only the physical successor count enters.  This is the route used to transport
the already established operator-level walk estimates to the finite
visited-state resolvent.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

set_option maxHeartbeats 800000

universe u v w

/-- A uniform whole-tail estimate and bounded physical branching give a
geometric norm estimate for every complete transfer power. -/
theorem norm_cmp116RestrictedVisitedTransferMatrix_pow_le_of_tail
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain] [Nonempty Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (K B : ℕ) (A rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (hRweak : 0 ≤ Rweak)
    (hTailBound :
      ∀ (n : ℕ)
        (source : CMP116RestrictedTransferState Label Domain carrier)
        (tail : List (CMP99WalkStep Label Domain)),
        tail ∈ cmp99AdmissibleTails successors source.1.domain n →
          ‖cmp116RestrictedVisitedTailProduct
              carrier domainActive R sigma source.2 tail‖ ≤
            A * rho ^ n * Rweak ^ (B * n))
    (n : ℕ) :
    ‖cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma ^ n‖ ≤
      A * (((K : ℝ) * rho * Rweak ^ B) ^ n) := by
  classical
  have hq0 : 0 ≤ (K : ℝ) * rho * Rweak ^ B := by positivity
  let state0 : CMP116RestrictedTransferState Label Domain carrier :=
    (⟨none, Classical.arbitrary Domain⟩,
      CMP116RestrictedVisitedState.empty carrier)
  letI : Nonempty
      (CMP116RestrictedTransferState Label Domain carrier) := ⟨state0⟩
  apply Matrix.linfty_opNorm_le_of_row_sum_le
  · exact mul_nonneg hA (pow_nonneg hq0 n)
  · intro source
    calc
      ∑ target,
          ‖(cmp116RestrictedVisitedTransferMatrix
              carrier domainActive successors R sigma ^ n) source target‖
          ≤
        ∑ target : CMP116RestrictedTransferState Label Domain carrier,
          ∑ tail ∈
              (cmp99AdmissibleTails successors source.1.domain n).filter
                (fun tail =>
                  cmp116RestrictedTransferTailState
                    carrier domainActive source tail = target),
            ‖cmp116RestrictedVisitedTailProduct
                carrier domainActive R sigma source.2 tail‖ := by
        apply Finset.sum_le_sum
        intro target _
        rw [cmp116RestrictedVisitedTransferMatrix_power_apply]
        unfold cmp116RestrictedVisitedGeneratedTailEntry
        exact norm_sum_le _ _
      _ =
        ∑ tail ∈ cmp99AdmissibleTails successors source.1.domain n,
          ‖cmp116RestrictedVisitedTailProduct
              carrier domainActive R sigma source.2 tail‖ :=
        Finset.sum_fiberwise_of_maps_to
          (fun _ _ => Finset.mem_univ _) _
      _ ≤
        ∑ _tail ∈ cmp99AdmissibleTails successors source.1.domain n,
          A * rho ^ n * Rweak ^ (B * n) := by
        apply Finset.sum_le_sum
        intro tail htailMem
        exact hTailBound n source tail htailMem
      _ =
        ((cmp99AdmissibleTails successors source.1.domain n).card : ℝ) *
          (A * rho ^ n * Rweak ^ (B * n)) := by simp
      _ ≤ ((K ^ n : ℕ) : ℝ) *
          (A * rho ^ n * Rweak ^ (B * n)) := by
        gcongr
        exact card_cmp99AdmissibleTails_le_pow
          successors K hK n source.1.domain
      _ = A * (((K : ℝ) * rho * Rweak ^ B) ^ n) := by
        push_cast
        rw [pow_mul]
        ring

/-- The same source ratio which sums the physical tails sums the complete
finite visited-state transfer powers. -/
theorem summable_cmp116RestrictedVisitedTransferMatrix_pow_of_tail
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain] [Nonempty Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (K B : ℕ) (A rho Rweak : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (hRweak : 0 ≤ Rweak)
    (htail :
      ∀ (n : ℕ)
        (source : CMP116RestrictedTransferState Label Domain carrier)
        (tail : List (CMP99WalkStep Label Domain)),
        tail ∈ cmp99AdmissibleTails successors source.1.domain n →
          ‖cmp116RestrictedVisitedTailProduct
              carrier domainActive R sigma source.2 tail‖ ≤
            A * rho ^ n * Rweak ^ (B * n))
    (hsmall : (K : ℝ) * rho * Rweak ^ B < 1) :
    Summable fun n : ℕ =>
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma ^ n := by
  have hq0 : 0 ≤ (K : ℝ) * rho * Rweak ^ B := by positivity
  have hgeom :
      Summable fun n : ℕ =>
        A * (((K : ℝ) * rho * Rweak ^ B) ^ n) := by
    exact
      (summable_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hq0]
        exact hsmall)).mul_left A
  exact Summable.of_norm_bounded hgeom
    (norm_cmp116RestrictedVisitedTransferMatrix_pow_le_of_tail
      carrier domainActive successors R sigma K B A rho Rweak
      hK hA hrho hRweak htail)

end

end YangMills.RG
