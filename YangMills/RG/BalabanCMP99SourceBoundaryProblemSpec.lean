/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceOmegaGeometry
import YangMills.RG.ShiftedCoerciveResolvent

/-!
# Honest boundary-problem specification for the CMP99 source propagators

The geometry of `Omega_n(Pi)` does not by itself define the printed
propagators.  This file introduces the first operator layer without replacing
the boundary problem by a support-compressed inverse.

`CMP99OmegaGreenBoundaryProblem` stores a precision `K_{Omega_r}` and a
two-sided Green operator `G'_{Omega_r}` on the already chosen admissible field
space.  `CMP99OmegaCovarianceBoundaryProblem` then records the printed
relation

`C_{Omega_r} = (Q' G'_{Omega_r}^2 Q'^*)^{-1}`

through both inverse equations.  The equations imply uniqueness and exact
second-resolvent identities at every consecutive transition.

This is deliberately a specification, not yet a producer: no instance is
constructed from `cmp99LocalizedPhysicalCovariance`, and no support-hardening
theorem is assumed.  The next analytic task is to instantiate the precision
and admissible field spaces from the literal CMP99 boundary conditions.
-/

namespace YangMills.RG

noncomputable section

variable {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q} {j : ℕ}

/-- A source geometry together with a genuine two-sided Green boundary
problem on its `j+2` regions. -/
structure CMP99OmegaGreenBoundaryProblem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  geometry : CMP99SourceOmegaGeometry cell j
  precision : Fin (j + 2) → E →L[ℝ] E
  green : Fin (j + 2) → E →L[ℝ] E
  green_comp_precision : ∀ r,
    (green r).comp (precision r) = ContinuousLinearMap.id ℝ E
  precision_comp_green : ∀ r,
    (precision r).comp (green r) = ContinuousLinearMap.id ℝ E

namespace CMP99OmegaGreenBoundaryProblem

/-- The two inverse equations make the source Green operator unique. -/
theorem green_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : CMP99OmegaGreenBoundaryProblem (cell := cell) (j := j) E)
    (r : Fin (j + 2)) (G : E →L[ℝ] E)
    (hGK : G.comp (P.precision r) = ContinuousLinearMap.id ℝ E) :
    G = P.green r := by
  apply ContinuousLinearMap.ext
  intro x
  have hPx : P.precision r (P.green r x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f x) (P.precision_comp_green r)
  have hGx : G (P.precision r (P.green r x)) = P.green r x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f (P.green r x)) hGK
  rw [hPx] at hGx
  exact hGx

/-- Exact Green-function resolvent identity across any consecutive source
transition. -/
theorem green_transition_resolvent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : CMP99OmegaGreenBoundaryProblem (cell := cell) (j := j) E)
    (r : Fin (j + 1)) :
    P.green (cmp99OmegaTransitionNextIndex r) -
        P.green (cmp99OmegaTransitionIndex r) =
      (P.green (cmp99OmegaTransitionNextIndex r)).comp
        ((P.precision (cmp99OmegaTransitionIndex r) -
            P.precision (cmp99OmegaTransitionNextIndex r)).comp
          (P.green (cmp99OmegaTransitionIndex r))) := by
  exact continuousLinearInverse_sub_eq_comp_sub_comp
    (P.precision (cmp99OmegaTransitionIndex r))
    (P.precision (cmp99OmegaTransitionNextIndex r))
    (P.green (cmp99OmegaTransitionIndex r))
    (P.green (cmp99OmegaTransitionNextIndex r))
    (P.green_comp_precision _)
    (P.precision_comp_green _)

end CMP99OmegaGreenBoundaryProblem

/-- The printed middle operator `Q' G'^2 Q'^*` at one source region. -/
def cmp99OmegaCovarianceMiddle
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P : CMP99OmegaGreenBoundaryProblem (cell := cell) (j := j) E)
    (Qprime : E →L[ℝ] F) (QprimeStar : F →L[ℝ] E)
    (r : Fin (j + 2)) : F →L[ℝ] F :=
  Qprime.comp ((P.green r).comp ((P.green r).comp QprimeStar))

/-- Source covariance boundary problem with the printed
`(Q' G'^2 Q'^*)^{-1}` equation, kept separate from the Green problem. -/
structure CMP99OmegaCovarianceBoundaryProblem
    (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    extends CMP99OmegaGreenBoundaryProblem (cell := cell) (j := j) E where
  Qprime : E →L[ℝ] F
  QprimeStar : F →L[ℝ] E
  covariance : Fin (j + 2) → F →L[ℝ] F
  covariance_comp_middle : ∀ r,
    (covariance r).comp
        (cmp99OmegaCovarianceMiddle toCMP99OmegaGreenBoundaryProblem
          Qprime QprimeStar r) = ContinuousLinearMap.id ℝ F
  middle_comp_covariance : ∀ r,
    (cmp99OmegaCovarianceMiddle toCMP99OmegaGreenBoundaryProblem
      Qprime QprimeStar r).comp (covariance r) =
        ContinuousLinearMap.id ℝ F

namespace CMP99OmegaCovarianceBoundaryProblem

/-- The printed covariance is unique once the Green boundary problem and the
two averaging maps are fixed. -/
theorem covariance_unique
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P : CMP99OmegaCovarianceBoundaryProblem
      (cell := cell) (j := j) E F)
    (r : Fin (j + 2)) (C : F →L[ℝ] F)
    (hCM : C.comp
        (cmp99OmegaCovarianceMiddle
          P.toCMP99OmegaGreenBoundaryProblem P.Qprime P.QprimeStar r) =
      ContinuousLinearMap.id ℝ F) :
    C = P.covariance r := by
  apply ContinuousLinearMap.ext
  intro x
  let M := cmp99OmegaCovarianceMiddle
    P.toCMP99OmegaGreenBoundaryProblem P.Qprime P.QprimeStar r
  have hMx : M (P.covariance r x) = x := by
    simpa only [M, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun f => f x) (P.middle_comp_covariance r)
  have hCx : C (M (P.covariance r x)) = P.covariance r x := by
    simpa only [M, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun f => f (P.covariance r x)) hCM
  rw [hMx] at hCx
  exact hCx

/-- Exact covariance resolvent identity across a consecutive source
transition.  The precision defect is now the difference of the literal
middle operators `Q' G'^2 Q'^*`, not a support-compression defect. -/
theorem covariance_transition_resolvent
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P : CMP99OmegaCovarianceBoundaryProblem
      (cell := cell) (j := j) E F)
    (r : Fin (j + 1)) :
    P.covariance (cmp99OmegaTransitionNextIndex r) -
        P.covariance (cmp99OmegaTransitionIndex r) =
      (P.covariance (cmp99OmegaTransitionNextIndex r)).comp
        ((cmp99OmegaCovarianceMiddle
              P.toCMP99OmegaGreenBoundaryProblem P.Qprime P.QprimeStar
              (cmp99OmegaTransitionIndex r) -
            cmp99OmegaCovarianceMiddle
              P.toCMP99OmegaGreenBoundaryProblem P.Qprime P.QprimeStar
              (cmp99OmegaTransitionNextIndex r)).comp
          (P.covariance (cmp99OmegaTransitionIndex r))) := by
  exact continuousLinearInverse_sub_eq_comp_sub_comp
    (cmp99OmegaCovarianceMiddle P.toCMP99OmegaGreenBoundaryProblem
      P.Qprime P.QprimeStar (cmp99OmegaTransitionIndex r))
    (cmp99OmegaCovarianceMiddle P.toCMP99OmegaGreenBoundaryProblem
      P.Qprime P.QprimeStar (cmp99OmegaTransitionNextIndex r))
    (P.covariance (cmp99OmegaTransitionIndex r))
    (P.covariance (cmp99OmegaTransitionNextIndex r))
    (P.covariance_comp_middle _)
    (P.middle_comp_covariance _)

end CMP99OmegaCovarianceBoundaryProblem

end

end YangMills.RG
