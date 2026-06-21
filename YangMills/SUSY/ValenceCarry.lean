/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.SUSY.WardComplex

/-!
# Cohomological valence carry

This module records the safe algebraic core of the "closed shell / valence
carry" idea.  A finite complex is equipped with a Ward differential `Q`, a
contracting homotopy `h`, and a valence projection `Π`.  The identity

`Q h + h Q = id - Π`

says that the non-valence sector is contractible.  Therefore a `Q`-closed
observable decomposes as

`F = Π F + Q (h F)`.

Under an exact Ward identity, the `Q`-exact summand is killed before any norm is
taken, so only the valence/collar defect must be estimated.  This is an
abstract finite interface only: it does not construct a supersymmetric
Yang--Mills theory, a fermionic Gaussian determinant, a matrix-tree theorem, or
the concrete gauge-RG activity.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.SUSY

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A finite cohomological-valence package.

`valence` is intentionally just a continuous linear map.  Later source work may
instantiate it as a collar projection, a harmonic/cohomology projection, a
Haar-singlet valence projection, or a Berezin/Hodge remainder. -/
structure ValenceCarryComplex
    (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] where
  /-- Ward/cohomological differential. -/
  Q : A →L[ℂ] A
  /-- Contracting homotopy on the closed-shell sector. -/
  homotopy : A →L[ℂ] A
  /-- Non-contractible valence/collar remainder. -/
  valence : A →L[ℂ] A
  /-- Nilpotence of the Ward differential. -/
  Q_square : Q.comp Q = 0
  /-- Closed-shell contraction identity. -/
  contracting :
    Q.comp homotopy + homotopy.comp Q =
      ContinuousLinearMap.id ℂ A - valence

namespace ValenceCarryComplex

/-- Closed observables for the valence complex. -/
def IsClosed (V : ValenceCarryComplex A) (F : A) : Prop :=
  V.Q F = 0

/-- Exact Ward identity: the expectation kills `Q`-exact terms. -/
def KillsExact (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ) : Prop :=
  ∀ F : A, expect (V.Q F) = 0

/-- Approximate Ward identity for the valence complex. -/
def WardDefectBound
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ) (defect : ℝ) :
    Prop :=
  ∀ F : A, ‖expect (V.Q F)‖ ≤ defect * ‖F‖

/-- Expected valence sector obeys a rooted/collar weight profile. -/
def ValenceExpectationBound
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (weight : A → ℝ) (amp : ℝ) : Prop :=
  ∀ F : A, ‖expect (V.valence F)‖ ≤ amp * weight F

/-- Norm-smallness of a transported valence carry.  This is the abstract
operator form of the desired RAP contraction; it is only a hypothesis here. -/
def CarryContraction
    (V : ValenceCarryComplex A) (carry : A →L[ℂ] A) (rho : ℝ) : Prop :=
  ‖V.valence.comp carry‖ ≤ rho ∧ rho < 1

/-- Packaged obligations for turning valence cancellation into a rooted bound.
The final field deliberately remains a proposition because the concrete
"valence lives on collars/holes" predicate depends on the future RG model. -/
structure RootedValenceCarryObligations
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ) where
  /-- Transport of nontrivial carry between local pieces. -/
  carry : A →L[ℂ] A
  /-- Rooted or modified-metric weight assigned to observables. -/
  weight : A → ℝ
  /-- Carry contraction parameter. -/
  rho : ℝ
  /-- Valence amplitude in the rooted norm. -/
  amp : ℝ
  /-- Transported carry is contractive. -/
  carry_contract : CarryContraction V carry rho
  /-- Expected valence obeys the rooted profile. -/
  valence_metric_bound : ValenceExpectationBound V expect weight amp
  /-- Placeholder for the concrete collar/hole support theorem. -/
  valence_hole_support : Prop

/-- Pointwise form of the contraction identity. -/
theorem contracting_apply (V : ValenceCarryComplex A) (F : A) :
    V.Q (V.homotopy F) + V.homotopy (V.Q F) =
      F - V.valence F := by
  have h := congrArg (fun T : A →L[ℂ] A => T F) V.contracting
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Nilpotence in pointwise form. -/
theorem Q_Q_apply (V : ValenceCarryComplex A) (F : A) :
    V.Q (V.Q F) = 0 := by
  have h := congrArg (fun T : A →L[ℂ] A => T F) V.Q_square
  simpa [ContinuousLinearMap.comp_apply] using h

/-- A closed observable is its valence part plus a `Q`-exact term. -/
theorem decomposition_of_closed
    (V : ValenceCarryComplex A) {F : A} (hF : V.IsClosed F) :
    F = V.valence F + V.Q (V.homotopy F) := by
  have h := V.contracting_apply F
  rw [hF, map_zero, add_zero] at h
  calc
    F = V.valence F + (F - V.valence F) := by abel
    _ = V.valence F + V.Q (V.homotopy F) := by rw [← h]

/-- Exact Ward cancellation leaves only the valence expectation. -/
theorem expect_eq_expect_valence_of_closed
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (hWard : V.KillsExact expect) {F : A} (hF : V.IsClosed F) :
    expect F = expect (V.valence F) := by
  have hdec :
      expect F = expect (V.valence F + V.Q (V.homotopy F)) :=
    congrArg expect (V.decomposition_of_closed hF)
  calc
    expect F = expect (V.valence F + V.Q (V.homotopy F)) := by
      exact hdec
    _ = expect (V.valence F) + expect (V.Q (V.homotopy F)) := by
      rw [map_add]
    _ = expect (V.valence F) + 0 := by
      rw [hWard (V.homotopy F)]
    _ = expect (V.valence F) := by rw [add_zero]

/-- Closed shell cancellation: if the valence projection vanishes on a closed
observable, exact Ward cancellation makes its expectation vanish. -/
theorem expect_eq_zero_of_closedShell
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (hWard : V.KillsExact expect) {F : A}
    (hF : V.IsClosed F) (hval : V.valence F = 0) :
    expect F = 0 := by
  rw [V.expect_eq_expect_valence_of_closed expect hWard hF, hval, map_zero]

/-- If a separate singlet/Haar projection leaves the expectation unchanged,
then a closed observable can be evaluated after both valence projection and
singlet projection. -/
theorem expect_eq_expect_singlet_valence_of_closed
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (singlet : A →L[ℂ] A)
    (hWard : V.KillsExact expect)
    (hsinglet : ∀ F : A, expect F = expect (singlet F))
    {F : A} (hF : V.IsClosed F) :
    expect F = expect (singlet (V.valence F)) := by
  rw [V.expect_eq_expect_valence_of_closed expect hWard hF]
  exact hsinglet (V.valence F)

/-- Approximate Ward cancellation: for a closed observable, the expectation
differs from the valence expectation only by the Ward defect of the homotopy
primitive. -/
theorem norm_expect_sub_expect_valence_le
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (defect : ℝ) (hWard : V.WardDefectBound expect defect)
    {F : A} (hF : V.IsClosed F) :
    ‖expect F - expect (V.valence F)‖ ≤
      defect * ‖V.homotopy F‖ := by
  have hdec :
      expect F = expect (V.valence F + V.Q (V.homotopy F)) :=
    congrArg expect (V.decomposition_of_closed hF)
  have hdiff :
      expect F - expect (V.valence F) =
        expect (V.Q (V.homotopy F)) := by
    rw [hdec, map_add]
    abel
  rw [hdiff]
  exact hWard (V.homotopy F)

/-- Exact valence profile bound for closed observables. -/
theorem expect_norm_le_of_valence_bound
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (hWard : V.KillsExact expect) (weight : A → ℝ) (amp : ℝ)
    (hval : V.ValenceExpectationBound expect weight amp)
    {F : A} (hF : V.IsClosed F) :
    ‖expect F‖ ≤ amp * weight F := by
  rw [V.expect_eq_expect_valence_of_closed expect hWard hF]
  exact hval F

/-- Approximate valence profile bound for closed observables. -/
theorem expect_norm_le_of_valence_bound_approx
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (defect : ℝ) (hWard : V.WardDefectBound expect defect)
    (weight : A → ℝ) (amp : ℝ)
    (hval : V.ValenceExpectationBound expect weight amp)
    {F : A} (hF : V.IsClosed F) :
    ‖expect F‖ ≤ amp * weight F + defect * ‖V.homotopy F‖ := by
  have hdec :
      expect F = expect (V.valence F + V.Q (V.homotopy F)) :=
    congrArg expect (V.decomposition_of_closed hF)
  calc
    ‖expect F‖
        = ‖expect (V.valence F) + expect (V.Q (V.homotopy F))‖ := by
          rw [hdec, map_add]
    _ ≤ ‖expect (V.valence F)‖ +
          ‖expect (V.Q (V.homotopy F))‖ := norm_add_le _ _
    _ ≤ amp * weight F + defect * ‖V.homotopy F‖ :=
          add_le_add (hval F) (hWard (V.homotopy F))

/-- Packaged exact consumer for rooted valence-carry obligations. -/
theorem expect_norm_le_of_rooted_obligations
    (V : ValenceCarryComplex A) (expect : A →L[ℂ] ℂ)
    (hWard : V.KillsExact expect)
    (B : V.RootedValenceCarryObligations expect)
    {F : A} (hF : V.IsClosed F) :
    ‖expect F‖ ≤ B.amp * B.weight F :=
  V.expect_norm_le_of_valence_bound expect hWard B.weight B.amp
    B.valence_metric_bound hF

end ValenceCarryComplex

end YangMills.SUSY
