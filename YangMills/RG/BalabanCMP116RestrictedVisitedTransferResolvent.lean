/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers
import YangMills.RG.BalabanCMP116RestrictedTransferActiveTarget
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Resolvent of the restricted visited-state transfer

Once the physical transfer powers are summable, their `tsum` is a genuine
two-sided inverse of `1 - T`.  The already proved active-target
factorization of `T(sigma) - T(1)` can therefore be consumed by the second
resolvent identity without expanding or rearranging any double series.
-/

namespace YangMills.RG

noncomputable section

universe u v w

set_option maxHeartbeats 800000

/-- Length-resummed finite-state transfer operator. -/
def cmp116RestrictedVisitedTransferResolvent
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    Matrix
      (CMP116RestrictedTransferState Label Domain carrier)
      (CMP116RestrictedTransferState Label Domain carrier)
      (Matrix Index Index ℂ) :=
  ∑' n : ℕ,
    cmp116RestrictedVisitedTransferMatrix
      carrier domainActive successors R sigma ^ n

/-- Summability of the physical transfer powers produces the right inverse
identity, with no separate nonsingularity hypothesis. -/
theorem cmp116RestrictedVisitedTransferResolvent_mul_one_sub
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma ^ n) :
    cmp116RestrictedVisitedTransferResolvent
          carrier domainActive successors R sigma *
        (1 - cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma) =
      1 := by
  letI : IsTopologicalRing
      (Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :=
    Matrix.topologicalRing
  exact @Summable.tsum_pow_mul_one_sub
    _ inferInstance inferInstance Matrix.topologicalRing inferInstance
      (cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma) hsum

/-- The same physical power sum is also a left inverse. -/
theorem one_sub_mul_cmp116RestrictedVisitedTransferResolvent
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma ^ n) :
    (1 - cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma) *
        cmp116RestrictedVisitedTransferResolvent
          carrier domainActive successors R sigma =
      1 := by
  letI : IsTopologicalRing
      (Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :=
    Matrix.topologicalRing
  exact @Summable.one_sub_mul_tsum_pow
    _ inferInstance inferInstance Matrix.topologicalRing inferInstance
      (cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma) hsum

/-- The complete restricted resolvent defect factors through the finite
subtype of contour-active target states.  The only analytic inputs are
summability of the two literal transfer-power families. -/
theorem cmp116RestrictedVisitedTransferResolvent_sub_one_eq_activeTargetFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (hsum :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma ^ n)
    (hsumOne :
      Summable fun n : ℕ =>
        cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R (fun _ => 1) ^ n) :
    let Tnew :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma
    let Tbase :=
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R (fun _ => 1)
    let Nnew :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors R sigma
    let Nbase :=
      cmp116RestrictedVisitedTransferResolvent
        carrier domainActive successors R (fun _ => 1)
    let p :=
      cmp116RestrictedTransferTargetActive carrier domainActive
    Nnew - Nbase =
      (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase)) *
        (Matrix.predicateColumnInclusion
          (R := Matrix Index Index ℂ) p * Nbase) := by
  dsimp only
  apply Matrix.resolvent_sub_resolvent_eq_mul_mul_of_factorization
  · exact cmp116RestrictedVisitedTransferResolvent_mul_one_sub
      carrier domainActive successors R sigma hsum
  · exact one_sub_mul_cmp116RestrictedVisitedTransferResolvent
      carrier domainActive successors R (fun _ => 1) hsumOne
  · exact
      cmp116RestrictedVisitedTransferMatrix_sub_one_eq_activeTargetFactorization
        carrier domainActive successors R sigma

end

end YangMills.RG
