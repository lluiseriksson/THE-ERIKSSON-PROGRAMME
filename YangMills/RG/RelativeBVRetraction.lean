/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# Relative BV retraction interface

This module records the algebraic core of a possible BV/BRST interpretation of
one gauge-RG step.  It is deliberately only a semantic interface: it does not
construct the BV complex for Yang--Mills, does not prove a Balaban background
field estimate, and does not identify holes with a concrete gauge-fixing
defect.

The contract is a relative strong-deformation-retraction identity

`id - lift.comp pushforward = brst.comp homotopy + homotopy.comp brst
  + boundaryDefect`.

For a BRST-closed observable, any expectation functional that kills BRST-exact
terms sees only the lifted effective observable and the boundary defect.  This
is the abstract "integrate/cancel first, norm later" bridge needed before one
can attach rooted modified-metric estimates to the defect.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

/-- A single relative BV/BRST renormalization step.

`Obs` is the ultraviolet/local observable space and `Eff` is the effective
infrared observable space.  The final field, `relative_sdr`, allows a boundary
defect; this is where a later with-holes construction can place gauge-chart,
cutoff, or small-field-boundary errors. -/
structure RelativeBVOneStep
    (Obs Eff : Type*) [NormedAddCommGroup Obs] [NormedSpace ℂ Obs]
    [NormedAddCommGroup Eff] [NormedSpace ℂ Eff] where
  /-- The ultraviolet BV/BRST differential. -/
  brst : Obs →L[ℂ] Obs
  /-- The effective infrared BV/BRST differential. -/
  effectiveBRST : Eff →L[ℂ] Eff
  /-- Exact UV-to-IR pushforward, conceptually fluctuation integration. -/
  pushforward : Obs →L[ℂ] Eff
  /-- IR-to-UV lift, conceptually the nonlinear background-field embedding. -/
  lift : Eff →L[ℂ] Obs
  /-- Chain homotopy contracting the UV-exact sector. -/
  homotopy : Obs →L[ℂ] Obs
  /-- Relative boundary defect, later to be supported near holes/cutoffs. -/
  boundaryDefect : Obs →L[ℂ] Obs
  /-- The pushforward is a left inverse to the lift. -/
  push_lift :
    pushforward.comp lift = ContinuousLinearMap.id ℂ Eff
  /-- The pushforward is a chain map. -/
  push_chain :
    pushforward.comp brst = effectiveBRST.comp pushforward
  /-- Relative strong-deformation-retraction identity with boundary defect. -/
  relative_sdr :
    ContinuousLinearMap.id ℂ Obs - lift.comp pushforward =
      brst.comp homotopy + homotopy.comp brst + boundaryDefect

namespace RelativeBVOneStep

variable {Obs Eff : Type*}
variable [NormedAddCommGroup Obs] [NormedSpace ℂ Obs]
variable [NormedAddCommGroup Eff] [NormedSpace ℂ Eff]

/-- BRST-closed observables in the ultraviolet complex. -/
def IsClosed (R : RelativeBVOneStep Obs Eff) (O : Obs) : Prop :=
  R.brst O = 0

/-- The expectation-level Ward identity used by the relative retraction. -/
def KillsBRSTExact (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ) :
    Prop :=
  ∀ F : Obs, expect (R.brst F) = 0

/-- Quantitative approximate Ward identity for the ultraviolet BRST operator. -/
def BRSTExpectationDefectBound
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ) (defect : ℝ) :
    Prop :=
  ∀ F : Obs, ‖expect (R.brst F)‖ ≤ defect * ‖F‖

/-- Boundary-defect bound after applying the expectation functional. -/
def BoundaryDefectExpectationBound
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ)
    (weight : Obs → ℝ) (amp : ℝ) : Prop :=
  ∀ O : Obs, ‖expect (R.boundaryDefect O)‖ ≤ amp * weight O

/-- Abstract norm-smallness of the homological perturbation kernel
`homotopy ∘ interaction`.  This is the finite-dimensional shadow of the
future rooted polymer contraction hypothesis `‖K δ‖ < 1`. -/
def HomotopyInteractionContractive
    (R : RelativeBVOneStep Obs Eff) (interaction : Obs →L[ℂ] Obs)
    (eta : ℝ) : Prop :=
  ‖R.homotopy.comp interaction‖ ≤ eta ∧ eta < 1

/-- Packaged analytic obligations for turning a relative BV step into a rooted
with-holes estimate.  The last field is intentionally a `Prop`: the concrete
support predicate depends on the future small-field chart/hole model. -/
structure RootedRelativeBVObligations
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ) where
  /-- Interaction inserted between homotopy propagators. -/
  interaction : Obs →L[ℂ] Obs
  /-- Rooted polymer/metric weight assigned to observables. -/
  weight : Obs → ℝ
  /-- Contraction parameter for the homological perturbation series. -/
  eta : ℝ
  /-- Boundary-defect amplitude in the rooted metric norm. -/
  boundaryAmp : ℝ
  /-- Quantitative `‖Kδ‖ < 1` hypothesis. -/
  homotopy_contract :
    HomotopyInteractionContractive R interaction eta
  /-- Expected boundary defect obeys the rooted metric profile. -/
  boundary_metric_bound :
    BoundaryDefectExpectationBound R expect weight boundaryAmp
  /-- Placeholder for the concrete "defect lives on holes/boundaries" theorem. -/
  boundary_hole_support : Prop

@[simp] theorem push_lift_apply (R : RelativeBVOneStep Obs Eff) (Oeff : Eff) :
    R.pushforward (R.lift Oeff) = Oeff := by
  have h := congrArg (fun f : Eff →L[ℂ] Eff => f Oeff) R.push_lift
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Pointwise form of the chain-map identity. -/
theorem push_chain_apply (R : RelativeBVOneStep Obs Eff) (O : Obs) :
    R.pushforward (R.brst O) = R.effectiveBRST (R.pushforward O) := by
  have h := congrArg (fun f : Obs →L[ℂ] Eff => f O) R.push_chain
  simpa [ContinuousLinearMap.comp_apply] using h

/-- A BRST-closed UV observable pushes forward to a closed effective
observable. -/
theorem effective_closed_of_closed (R : RelativeBVOneStep Obs Eff) {O : Obs}
    (hO : R.IsClosed O) :
    R.effectiveBRST (R.pushforward O) = 0 := by
  rw [← R.push_chain_apply O, hO, map_zero]

/-- Pointwise form of the relative strong-deformation-retraction identity. -/
theorem relative_sdr_apply (R : RelativeBVOneStep Obs Eff) (O : Obs) :
    O - R.lift (R.pushforward O) =
      R.brst (R.homotopy O) + R.homotopy (R.brst O) +
        R.boundaryDefect O := by
  have h := congrArg (fun f : Obs →L[ℂ] Obs => f O) R.relative_sdr
  simpa [ContinuousLinearMap.comp_apply] using h

/-- For closed observables the middle homotopy term drops from the relative
identity. -/
theorem relative_sdr_apply_of_closed (R : RelativeBVOneStep Obs Eff) {O : Obs}
    (hO : R.IsClosed O) :
    O - R.lift (R.pushforward O) =
      R.brst (R.homotopy O) + R.boundaryDefect O := by
  calc
    O - R.lift (R.pushforward O)
        = R.brst (R.homotopy O) + R.homotopy (R.brst O) +
            R.boundaryDefect O := R.relative_sdr_apply O
    _ = R.brst (R.homotopy O) + R.boundaryDefect O := by
          rw [hO, map_zero, add_zero]

/-- Applying an expectation functional to the relative identity for a closed
observable leaves a BRST-exact term plus the boundary defect. -/
theorem expectation_relative_decomposition_of_closed
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ) {O : Obs}
    (hO : R.IsClosed O) :
    expect O - expect (R.lift (R.pushforward O)) =
      expect (R.brst (R.homotopy O)) +
        expect (R.boundaryDefect O) := by
  have h := congrArg expect (R.relative_sdr_apply_of_closed hO)
  simpa [map_sub, map_add] using h

/-- Exact Ward cancellation: a closed observable differs from its lifted
effective pushforward only by the expected boundary defect. -/
theorem expectation_defect_identity
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ)
    (hWard : KillsBRSTExact R expect) {O : Obs} (hO : R.IsClosed O) :
    expect O - expect (R.lift (R.pushforward O)) =
      expect (R.boundaryDefect O) := by
  calc
    expect O - expect (R.lift (R.pushforward O))
        = expect (R.brst (R.homotopy O)) +
            expect (R.boundaryDefect O) :=
          expectation_relative_decomposition_of_closed R expect hO
    _ = 0 + expect (R.boundaryDefect O) := by rw [hWard (R.homotopy O)]
    _ = expect (R.boundaryDefect O) := by rw [zero_add]

/-- Norm version of exact relative Ward cancellation. -/
theorem expectation_defect_bound
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ)
    (hWard : KillsBRSTExact R expect) (weight : Obs → ℝ) (amp : ℝ)
    (hboundary : BoundaryDefectExpectationBound R expect weight amp)
    {O : Obs} (hO : R.IsClosed O) :
    ‖expect O - expect (R.lift (R.pushforward O))‖ ≤ amp * weight O := by
  rw [expectation_defect_identity R expect hWard hO]
  exact hboundary O

/-- Approximate Ward cancellation for a closed observable: the only extra term
is the Ward defect applied to the homotopy primitive. -/
theorem expectation_defect_bound_of_approx_ward
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ)
    (defect : ℝ) (hWard : BRSTExpectationDefectBound R expect defect)
    {O : Obs} (hO : R.IsClosed O) :
    ‖expect O - expect (R.lift (R.pushforward O))‖ ≤
      defect * ‖R.homotopy O‖ + ‖expect (R.boundaryDefect O)‖ := by
  calc
    ‖expect O - expect (R.lift (R.pushforward O))‖
        = ‖expect (R.brst (R.homotopy O)) +
            expect (R.boundaryDefect O)‖ := by
          rw [expectation_relative_decomposition_of_closed R expect hO]
    _ ≤ ‖expect (R.brst (R.homotopy O))‖ +
          ‖expect (R.boundaryDefect O)‖ := norm_add_le _ _
    _ ≤ defect * ‖R.homotopy O‖ +
          ‖expect (R.boundaryDefect O)‖ :=
          add_le_add (hWard (R.homotopy O)) (le_refl _)

/-- Packaged consumer for the exact relative BV obligations.  This is still an
abstract estimate: it does not assert that Yang--Mills supplies the required
homotopy contraction or hole support. -/
theorem expectation_defect_bound_of_rooted_obligations
    (R : RelativeBVOneStep Obs Eff) (expect : Obs →L[ℂ] ℂ)
    (hWard : KillsBRSTExact R expect)
    (B : RootedRelativeBVObligations R expect)
    {O : Obs} (hO : R.IsClosed O) :
    ‖expect O - expect (R.lift (R.pushforward O))‖ ≤
      B.boundaryAmp * B.weight O :=
  expectation_defect_bound R expect hWard B.weight B.boundaryAmp
    B.boundary_metric_bound hO

end RelativeBVOneStep

end YangMills.RG
