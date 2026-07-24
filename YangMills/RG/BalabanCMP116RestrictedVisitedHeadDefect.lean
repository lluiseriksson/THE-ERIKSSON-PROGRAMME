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

/-- Left rectangular factor obtained by applying the physical head readout
to the left leg of a block-matrix factorization. -/
def cmp116RestrictedHeadReadoutProductLeft
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index Middle : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Middle]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (A :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        Middle (Matrix Index Index ℂ)) :
    Matrix Index (Middle × Index) ℂ :=
  fun row middleInput =>
    (∑ head,
      CMP116RestrictedVisitedState.transitionWeight
          carrier sigma (CMP116RestrictedVisitedState.empty carrier)
          (domainActive head) •
        (R0 head *
          A (cmp116RestrictedTransferHeadState
              (Label := Label) carrier domainActive head)
            middleInput.1)) row middleInput.2

/-- Right rectangular factor summing the terminal visited state of the
right leg of a block-matrix factorization. -/
def cmp116RestrictedHeadReadoutProductRight
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index Middle : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Middle]
    (carrier : Finset Delta)
    (B :
      Matrix Middle
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :
    Matrix (Middle × Index) Index ℂ :=
  fun middleInput col =>
    (∑ target, B middleInput.1 target) middleInput.2 col

/-- Applying the physical head readout to a block product preserves its
finite intermediate factorization after adjoining the physical coordinate
index. -/
theorem cmp116RestrictedVisitedTransferHeadReadout_mul_eq_productFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index Middle : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Middle]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (A :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        Middle (Matrix Index Index ℂ))
    (B :
      Matrix Middle
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) :
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma (A * B) =
      cmp116RestrictedHeadReadoutProductLeft
          carrier domainActive R0 sigma A *
        cmp116RestrictedHeadReadoutProductRight carrier B := by
  classical
  ext row col
  simp only [cmp116RestrictedVisitedTransferHeadReadout,
    cmp116RestrictedHeadReadoutProductLeft,
    cmp116RestrictedHeadReadoutProductRight,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hcomm
      (F :
        Domain → Index →
          CMP116RestrictedTransferState Label Domain carrier →
          Middle → Index → ℂ) :
      (∑ head, ∑ input, ∑ target, ∑ middle, ∑ inner,
          F head input target middle inner) =
        ∑ middleInput : Middle × Index,
          ∑ target, ∑ head, ∑ input,
            F head input target middleInput.1 middleInput.2 := by
    calc
      (∑ head, ∑ input, ∑ target, ∑ middle, ∑ inner,
          F head input target middle inner) =
          ∑ head, ∑ target, ∑ input, ∑ middle, ∑ inner,
            F head input target middle inner := by
        apply Fintype.sum_congr
        intro head
        rw [Finset.sum_comm]
      _ = ∑ target, ∑ head, ∑ input, ∑ middle, ∑ inner,
            F head input target middle inner := by
        rw [Finset.sum_comm]
      _ = ∑ target, ∑ head, ∑ input,
            ∑ middleInput : Middle × Index,
              F head input target middleInput.1 middleInput.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ target, ∑ head, ∑ middleInput : Middle × Index,
            ∑ input,
              F head input target middleInput.1 middleInput.2 := by
        apply Fintype.sum_congr
        intro target
        apply Fintype.sum_congr
        intro head
        rw [Finset.sum_comm]
      _ = ∑ target, ∑ middleInput : Middle × Index,
            ∑ head, ∑ input,
              F head input target middleInput.1 middleInput.2 := by
        apply Fintype.sum_congr
        intro target
        rw [Finset.sum_comm]
      _ = ∑ middleInput : Middle × Index,
            ∑ target, ∑ head, ∑ input,
              F head input target middleInput.1 middleInput.2 := by
        rw [Finset.sum_comm]
  simpa only [mul_assoc] using
    hcomm (fun head input target middle inner =>
      CMP116RestrictedVisitedState.transitionWeight
          carrier sigma (CMP116RestrictedVisitedState.empty carrier)
          (domainActive head) *
        (R0 head row input *
          (A (cmp116RestrictedTransferHeadState
              (Label := Label) carrier domainActive head)
              middle input inner *
            B middle target inner col)))

/-- The physical readout of the complete transfer-resolvent defect factors
through contour-active target states times physical coordinates. -/
theorem cmp116RestrictedVisitedTransferHeadReadout_resolvent_sub_one_eq_activeTargetFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R0 : Domain → Matrix Index Index ℂ)
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
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) (Nnew - Nbase) =
      cmp116RestrictedHeadReadoutProductLeft
          carrier domainActive R0 (fun _ => 1)
          (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase)) *
        cmp116RestrictedHeadReadoutProductRight
          carrier
          (Matrix.predicateColumnInclusion
            (R := Matrix Index Index ℂ) p * Nbase) := by
  dsimp only
  rw [
    cmp116RestrictedVisitedTransferResolvent_sub_one_eq_activeTargetFactorization
      carrier domainActive successors R sigma hsum hsumOne,
    cmp116RestrictedVisitedTransferHeadReadout_mul_eq_productFactorization]

/-- Concatenate two left rectangular factors along a disjoint finite
intermediate index. -/
def Matrix.sumFactorLeft
    {Row Kappa Lambda R : Type*}
    (A : Matrix Row Kappa R)
    (C : Matrix Row Lambda R) :
    Matrix Row (Kappa ⊕ Lambda) R :=
  fun row intermediate =>
    Sum.elim (A row) (C row) intermediate

/-- Stack two right rectangular factors along a disjoint finite intermediate
index. -/
def Matrix.sumFactorRight
    {Col Kappa Lambda R : Type*}
    (B : Matrix Kappa Col R)
    (D : Matrix Lambda Col R) :
    Matrix (Kappa ⊕ Lambda) Col R :=
  fun intermediate col =>
    Sum.elim (fun kappa => B kappa col) (fun lambda => D lambda col)
      intermediate

/-- Horizontal concatenation and vertical stacking turn a sum of two
finite-rank products into one finite-rank product. -/
theorem Matrix.sumFactorLeft_mul_sumFactorRight
    {Index Kappa Lambda R : Type*}
    [Fintype Kappa] [Fintype Lambda]
    [Fintype Index] [Semiring R]
    (A : Matrix Index Kappa R)
    (B : Matrix Kappa Index R)
    (C : Matrix Index Lambda R)
    (D : Matrix Lambda Index R) :
    Matrix.sumFactorLeft A C * Matrix.sumFactorRight B D =
      A * B + C * D := by
  ext row col
  simp [Matrix.mul_apply, Matrix.sumFactorLeft,
    Matrix.sumFactorRight, Fintype.sum_sum_type]

/-- The complete physical readout defect has one finite factorization.  Its
intermediate index is the disjoint union of active heads and active transfer
targets, each paired with one physical coordinate. -/
theorem cmp116RestrictedVisitedTransferHeadReadout_resolvent_sub_one_eq_finiteFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R0 : Domain → Matrix Index Index ℂ)
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
    let AHead :=
      cmp116RestrictedHeadDefectLeft carrier domainActive R0 sigma
    let BHead :=
      cmp116RestrictedHeadDefectRight
        (Label := Label) carrier domainActive Nnew
    let ADynamic :=
      cmp116RestrictedHeadReadoutProductLeft
        carrier domainActive R0 (fun _ => 1)
        (Nnew * Matrix.predicateColumnRestriction p (Tnew - Tbase))
    let BDynamic :=
      cmp116RestrictedHeadReadoutProductRight
        carrier
        (Matrix.predicateColumnInclusion
          (R := Matrix Index Index ℂ) p * Nbase)
    cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma Nnew -
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 (fun _ => 1) Nbase =
      Matrix.sumFactorLeft AHead ADynamic *
        Matrix.sumFactorRight BHead BDynamic := by
  dsimp only
  rw [
    cmp116RestrictedVisitedTransferHeadReadout_sub_eq_headDefect_add_resolventDefect,
    cmp116RestrictedVisitedTransferHeadReadout_sub_one_eq_headActiveFactorization,
    cmp116RestrictedVisitedTransferHeadReadout_resolvent_sub_one_eq_activeTargetFactorization
      carrier domainActive successors R0 R sigma hsum hsumOne,
    Matrix.sumFactorLeft_mul_sumFactorRight]

end

end YangMills.RG
