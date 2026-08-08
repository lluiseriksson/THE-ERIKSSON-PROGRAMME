/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers
import YangMills.RG.BalabanCMP116RestrictedTransferActiveTarget
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

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

/-- Finite head readout of an augmented transfer operator.  This is the
linear operation that turns a transfer resolvent back into the physical
covariance matrix. -/
def cmp116RestrictedVisitedTransferHeadReadout
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
    Matrix Index Index ℂ :=
  ∑ head,
    CMP116RestrictedVisitedState.transitionWeight
        carrier sigma (CMP116RestrictedVisitedState.empty carrier)
        (domainActive head) •
      (R0 head *
        ∑ target,
          N (cmp116RestrictedTransferHeadState
              (Label := Label) carrier domainActive head)
            target)

/-- The finite head readout is a continuous complex-linear map. -/
noncomputable def cmp116RestrictedVisitedTransferHeadReadoutCLM
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [Fintype Domain]
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (R0 : Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    (Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ)) →L[ℂ]
      Matrix Index Index ℂ := by
  let L :
      (Matrix
          (CMP116RestrictedTransferState Label Domain carrier)
          (CMP116RestrictedTransferState Label Domain carrier)
          (Matrix Index Index ℂ)) →ₗ[ℂ]
        Matrix Index Index ℂ := {
    toFun := cmp116RestrictedVisitedTransferHeadReadout
      carrier domainActive R0 sigma
    map_add' := by
      intro left right
      ext i j
      simp [cmp116RestrictedVisitedTransferHeadReadout, Matrix.mul_apply,
        Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum, mul_add]
      simp only [Finset.sum_add_distrib]
    map_smul' := by
      intro scalar N
      ext i j
      simp [cmp116RestrictedVisitedTransferHeadReadout, Matrix.mul_apply,
        Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum,
        mul_assoc, mul_comm]
  }
  have hL :
      Continuous
        (L :
          (Matrix
              (CMP116RestrictedTransferState Label Domain carrier)
              (CMP116RestrictedTransferState Label Domain carrier)
              (Matrix Index Index ℂ)) →
            Matrix Index Index ℂ) :=
    @LinearMap.continuous_of_finiteDimensional
      ℂ inferInstance
      (Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (Matrix Index Index ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (Module.Finite.matrix) L
  exact ⟨L, hL⟩

/-- A finite transfer-power layer is definitionally the head readout of that
power. -/
theorem cmp116RestrictedVisitedTransferPowerLayer_eq_headReadout
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
    (n : ℕ) :
    cmp116RestrictedVisitedTransferPowerLayer
        carrier domainActive successors R0 R sigma n =
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma
        (cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma ^ n) :=
  rfl

/-- Summing all finite walk layers is exactly one finite head readout of the
transfer resolvent. -/
theorem tsum_cmp116RestrictedVisitedTransferPowerLayer_eq_headReadout_resolvent
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
          carrier domainActive successors R sigma ^ n) :
    (∑' n : ℕ,
        cmp116RestrictedVisitedTransferPowerLayer
          carrier domainActive successors R0 R sigma n) =
      cmp116RestrictedVisitedTransferHeadReadout
        carrier domainActive R0 sigma
        (cmp116RestrictedVisitedTransferResolvent
          carrier domainActive successors R sigma) := by
  let T :
      Matrix
        (CMP116RestrictedTransferState Label Domain carrier)
        (CMP116RestrictedTransferState Label Domain carrier)
        (Matrix Index Index ℂ) :=
    cmp116RestrictedVisitedTransferMatrix
      carrier domainActive successors R sigma
  let L :
      (Matrix
          (CMP116RestrictedTransferState Label Domain carrier)
          (CMP116RestrictedTransferState Label Domain carrier)
          (Matrix Index Index ℂ)) →L[ℂ]
        Matrix Index Index ℂ :=
    cmp116RestrictedVisitedTransferHeadReadoutCLM
      carrier domainActive R0 sigma
  have hmap : L (∑' n : ℕ, T ^ n) = ∑' n : ℕ, L (T ^ n) :=
    L.map_tsum hsum
  change (∑' n : ℕ, L (T ^ n)) = L (∑' n : ℕ, T ^ n)
  exact hmap.symm

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
