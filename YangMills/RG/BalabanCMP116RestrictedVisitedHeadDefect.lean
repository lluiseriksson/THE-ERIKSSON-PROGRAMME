/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferResolvent

/-!
# Finite-rank defect of the restricted head readout

The complete covariance readout depends on the contour twice: through the
transfer resolvent and through the weakening weight of the distinguished
head.  This module isolates the latter dependence and factors it exactly
through the finite subtype of contour-active physical heads.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- A physical head is contour-active when its domain contains at least one
coordinate of the restricted carrier. -/
def cmp116RestrictedHeadActive
    {Domain : Type v} {Delta : Type w} [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (head : Domain) : Prop :=
  (domainActive head ∩ carrier).Nonempty

instance instDecidableCmp116RestrictedHeadActive
    {Domain : Type v} {Delta : Type w} [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (head : Domain) :
    Decidable (cmp116RestrictedHeadActive carrier domainActive head) :=
  Finset.decidableNonempty

/-- An inactive head has weakening weight one, for every restricted
coupling. -/
theorem cmp116RestrictedHeadWeight_eq_one_of_not_active
    {Domain : Type v} {Delta : Type w} [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (sigma : Delta → ℂ)
    (head : Domain)
    (hinactive :
      ¬ cmp116RestrictedHeadActive carrier domainActive head) :
    CMP116RestrictedVisitedState.transitionWeight
        carrier sigma (CMP116RestrictedVisitedState.empty carrier)
        (domainActive head) =
      1 := by
  have hinter : domainActive head ∩ carrier = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hinactive
  simp [CMP116RestrictedVisitedState.transitionWeight,
    CMP116RestrictedVisitedState.newlyActive, hinter,
    cmp116ComplexWeakeningMonomial]

/-- Left rectangular factor carrying the contour-dependent head-weight
difference. -/
def cmp116RestrictedHeadDefectLeft
    {Domain : Type v} {Delta : Type w}
    [Fintype Domain] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    Matrix Index
      ({head : Domain //
        cmp116RestrictedHeadActive carrier domainActive head} × Index) ℂ :=
  fun row headInput =>
    (CMP116RestrictedVisitedState.transitionWeight
        carrier sigma (CMP116RestrictedVisitedState.empty carrier)
          (domainActive headInput.1.1) - 1) *
      R0 headInput.1.1 row headInput.2

/-- Right rectangular factor reading the complete row of a visited-state
operator attached to one contour-active physical head. -/
def cmp116RestrictedHeadDefectRight
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (N :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :
    Matrix
      ({head : Domain //
        cmp116RestrictedHeadActive carrier domainActive head} × Index)
      Index ℂ :=
  fun headInput col =>
    (∑ target,
      N (cmp116RestrictedTransferHeadState
          (Label := Label) carrier domainActive headInput.1.1)
        target) headInput.2 col

/-- The change of head weakening weights at a fixed visited-state operator
factors exactly through active heads times physical coordinates. -/
theorem cmp116RestrictedVisitedTransferHeadReadout_sub_one_eq_headActiveFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (N :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma N -
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) N =
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma *
        cmp116RestrictedHeadDefectRight
          (Label := Label) carrier domainActive N := by
  classical
  have hone :
      ∀ head : Domain,
        CMP116RestrictedVisitedState.transitionWeight
            carrier (fun _ => 1)
              (CMP116RestrictedVisitedState.empty carrier)
              (domainActive head) =
          1 := by
    intro head
    simp [CMP116RestrictedVisitedState.transitionWeight,
      cmp116ComplexWeakeningMonomial]
  calc
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma N -
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) N =
        ∑ head : Domain,
          (CMP116RestrictedVisitedState.transitionWeight
              carrier sigma (CMP116RestrictedVisitedState.empty carrier)
              (domainActive head) - 1) •
            (R0 head *
              ∑ target,
                N (cmp116RestrictedTransferHeadState
                    (Label := Label) carrier domainActive head)
                  target) := by
      unfold cmp116RestrictedVisitedTransferHeadReadout
      simp_rw [hone, one_smul, sub_smul]
      simp_rw [one_smul]
      exact
        (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset Domain))
          (fun head =>
            CMP116RestrictedVisitedState.transitionWeight
                carrier sigma (CMP116RestrictedVisitedState.empty carrier)
                (domainActive head) •
              (R0 head *
                ∑ target,
                  N (cmp116RestrictedTransferHeadState
                      (Label := Label) carrier domainActive head)
                    target))
          (fun head =>
            R0 head *
              ∑ target,
                N (cmp116RestrictedTransferHeadState
                    (Label := Label) carrier domainActive head)
                  target)).symm
    _ =
        ∑ head :
            {head : Domain //
              cmp116RestrictedHeadActive carrier domainActive head},
          (CMP116RestrictedVisitedState.transitionWeight
              carrier sigma (CMP116RestrictedVisitedState.empty carrier)
              (domainActive head.1) - 1) •
            (R0 head.1 *
              ∑ target,
                N (cmp116RestrictedTransferHeadState
                    (Label := Label) carrier domainActive head.1)
                  target) := by
      rw [← Fintype.sum_subtype_add_sum_subtype
        (cmp116RestrictedHeadActive carrier domainActive)
        (fun head =>
          (CMP116RestrictedVisitedState.transitionWeight
              carrier sigma (CMP116RestrictedVisitedState.empty carrier)
              (domainActive head) - 1) •
            (R0 head *
              ∑ target,
                N (cmp116RestrictedTransferHeadState
                    (Label := Label) carrier domainActive head)
                  target))]
      have hinactive :
          (∑ head :
              {head : Domain //
                ¬ cmp116RestrictedHeadActive carrier domainActive head},
            (CMP116RestrictedVisitedState.transitionWeight
                carrier sigma (CMP116RestrictedVisitedState.empty carrier)
                (domainActive head.1) - 1) •
              (R0 head.1 *
                ∑ target,
                  N (cmp116RestrictedTransferHeadState
                      (Label := Label) carrier domainActive head.1)
                    target)) =
            0 := by
        apply Finset.sum_eq_zero
        intro head _hhead
        rw [cmp116RestrictedHeadWeight_eq_one_of_not_active
          carrier domainActive sigma head.1 head.2]
        simp
      rw [hinactive, add_zero]
    _ =
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma *
        cmp116RestrictedHeadDefectRight
          (Label := Label) carrier domainActive N := by
      ext row col
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, cmp116RestrictedHeadDefectLeft,
        cmp116RestrictedHeadDefectRight, Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro head
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro input
      ring

/-- Exact telescope separating the contour dependence of the head readout
from the contour dependence of the transfer resolvent. -/
theorem cmp116RestrictedVisitedTransferHeadReadout_sub_eq_headDefect_add_resolventDefect
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (Nnew Nbase :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma Nnew -
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) Nbase =
      (cmp116RestrictedVisitedTransferHeadReadout
          carrier domainActive R0 sigma Nnew -
        cmp116RestrictedVisitedTransferHeadReadout
          carrier domainActive R0 (fun _ => 1) Nnew) +
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) (Nnew - Nbase) := by
  let L := cmp116RestrictedVisitedTransferHeadReadoutCLM
    (Label := Label) carrier domainActive R0 (fun _ => 1)
  rw [show
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) (Nnew - Nbase) =
      L (Nnew - Nbase) by rfl]
  rw [map_sub]
  change
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma Nnew -
      L Nbase =
    (cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma Nnew - L Nnew) +
      (L Nnew - L Nbase)
  abel

end

end YangMills.RG
