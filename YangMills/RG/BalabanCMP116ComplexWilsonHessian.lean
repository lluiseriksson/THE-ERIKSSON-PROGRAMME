/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116WilsonHessianDifferential
import YangMills.RG.PhysicalGaugeCMP116Dictionary
import YangMills.RG.SUNAdjointModelInstance

/-!
# Holomorphic Wilson Hessian on the CMP116 contour

The real physical Hessian is insufficient on the Cauchy contours of equation
(2.14).  This module constructs the literal holomorphic continuation before
introducing any estimate.

For one complex matrix coordinate `Z_b` on each positive physical bond,
positive and negative oriented edges are

`exp(Z_b) U_b` and `U_b⁻¹ exp(-Z_b)`.

At a unitary physical background the inverse is represented by the conjugate
transpose of the *fixed* background matrix.  No conjugation is applied to the
complex variable `Z`; consequently the resulting Wilson action is holomorphic.
Its complex Fréchet Hessian is evaluated at an arbitrary contour background
`Z`, and then written as a finite matrix in the canonical `su(Nc)` coordinate
basis.

This module does not yet identify the CMP116 `sigma` variables with a contour
background `Z`, add gauge fixing, invert the precision, or prove (2.16).
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Complexified physical bond coordinates. -/
abbrev PhysicalComplexMatrixTangent (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N → Matrix (Fin Nc) (Fin Nc) ℂ

/-- Evaluation at one physical bond as a complex continuous linear map. -/
def physicalComplexBondEvalCLM (b : PhysicalBond d N) :
    PhysicalComplexMatrixTangent d N Nc →L[ℂ]
      Matrix (Fin Nc) (Fin Nc) ℂ :=
  ContinuousLinearMap.proj b

/-- Positive oriented edge on the holomorphic contour chart. -/
def complexWilsonPositiveBondMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (b : PhysicalBond d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  physicalMatrixExp (Z b) * (U (positiveEdgeOfPhysicalBond b)).val

/-- Oriented edge on the holomorphic contour chart.  The negative edge uses
the inverse of the fixed unitary background and `exp(-Z_b)` on the right. -/
def complexWilsonOrientedEdgeMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (e : ConcreteEdge d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    complexWilsonPositiveBondMatrix U Z (physicalBondOfEdge e)
  else
    Matrix.conjTranspose
        (U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))).val *
      physicalMatrixExp (-(Z (physicalBondOfEdge e)))

@[simp] theorem complexWilsonOrientedEdgeMatrix_positive
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (b : PhysicalBond d N) :
    complexWilsonOrientedEdgeMatrix U Z (positiveEdgeOfPhysicalBond b) =
      complexWilsonPositiveBondMatrix U Z b := by
  cases b
  simp [complexWilsonOrientedEdgeMatrix, positiveEdgeOfPhysicalBond,
    physicalBondOfEdge]

/-- The positive contour edge is holomorphic in all bond coordinates. -/
theorem analyticAt_complexWilsonPositiveBondMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (b : PhysicalBond d N) :
    AnalyticAt ℂ (fun W => complexWilsonPositiveBondMatrix U W b) Z := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have heval : AnalyticAt ℂ
      (fun W : PhysicalComplexMatrixTangent d N Nc => W b) Z :=
    (physicalComplexBondEvalCLM b).analyticAt Z
  have hexp : AnalyticAt ℂ
      (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => NormedSpace.exp A) (Z b) :=
    NormedSpace.exp_analytic (Z b)
  exact (hexp.comp
    (f := fun W : PhysicalComplexMatrixTangent d N Nc => W b)
    heval).mul analyticAt_const

/-- The negative contour edge is holomorphic because the conjugate transpose
is applied only to the fixed background, never to the contour variable. -/
theorem analyticAt_complexWilsonOrientedEdgeMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (e : ConcreteEdge d N) :
    AnalyticAt ℂ (fun W => complexWilsonOrientedEdgeMatrix U W e) Z := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  by_cases h : e.sign
  · simp only [complexWilsonOrientedEdgeMatrix, h, if_true]
    exact analyticAt_complexWilsonPositiveBondMatrix U Z
      (physicalBondOfEdge e)
  · simp only [complexWilsonOrientedEdgeMatrix, h, if_false]
    have heval : AnalyticAt ℂ
        (fun W : PhysicalComplexMatrixTangent d N Nc =>
          -(W (physicalBondOfEdge e))) Z :=
      ((physicalComplexBondEvalCLM (physicalBondOfEdge e)).analyticAt Z).neg
    have hexp : AnalyticAt ℂ
        (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => NormedSpace.exp A)
        (-(Z (physicalBondOfEdge e))) :=
      NormedSpace.exp_analytic _
    exact analyticAt_const.mul (hexp.comp
      (f := fun W : PhysicalComplexMatrixTangent d N Nc =>
        -(W (physicalBondOfEdge e)))
      heval)

/-- At the center of the complex contour chart the oriented edge is exactly
the oriented edge of the existing real ambient chart. -/
@[simp] theorem complexWilsonOrientedEdgeMatrix_zero
    (U : PhysicalGaugeBackground d N Nc)
    (e : ConcreteEdge d N) :
    complexWilsonOrientedEdgeMatrix U 0 e =
      ambientOrientedEdgeMatrix U 0 e := by
  by_cases h : e.sign
  · simp [complexWilsonOrientedEdgeMatrix, ambientOrientedEdgeMatrix,
      complexWilsonPositiveBondMatrix, ambientPositiveBondMatrix, h]
  · simp [complexWilsonOrientedEdgeMatrix, ambientOrientedEdgeMatrix,
      complexWilsonPositiveBondMatrix, ambientPositiveBondMatrix, h]

/-- Holomorphic four-edge plaquette word. -/
def complexWilsonPlaquetteHolonomy
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((complexWilsonOrientedEdgeMatrix U Z (p.edges 0) *
      complexWilsonOrientedEdgeMatrix U Z (p.edges 1)) *
    complexWilsonOrientedEdgeMatrix U Z (p.edges 2)) *
      complexWilsonOrientedEdgeMatrix U Z (p.edges 3)

theorem analyticAt_complexWilsonPlaquetteHolonomy
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) :
    AnalyticAt ℂ (fun W => complexWilsonPlaquetteHolonomy U W p) Z := by
  exact (((analyticAt_complexWilsonOrientedEdgeMatrix U Z (p.edges 0)).mul
    (analyticAt_complexWilsonOrientedEdgeMatrix U Z (p.edges 1))).mul
      (analyticAt_complexWilsonOrientedEdgeMatrix U Z (p.edges 2))).mul
        (analyticAt_complexWilsonOrientedEdgeMatrix U Z (p.edges 3))

/-- The complex plaquette word agrees exactly with the existing ambient word
at the center of the contour. -/
@[simp] theorem complexWilsonPlaquetteHolonomy_zero
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    complexWilsonPlaquetteHolonomy U 0 p =
      ambientPlaquetteHolonomy U 0 p := by
  simp [complexWilsonPlaquetteHolonomy, ambientPlaquetteHolonomy]

/-- Complex analytic continuation of `1 - Re tr U(p)`.  On the physical real
slice its real part is the existing Wilson plaquette action. -/
def complexWilsonPlaquetteAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) : ℂ :=
  1 - Matrix.trace (complexWilsonPlaquetteHolonomy U Z p)

/-- One matrix entry as a complex continuous linear functional. -/
def complexMatrixEntryCLM (i j : Fin Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Nc => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin Nc => Fin Nc → ℂ) i)

theorem analyticAt_complexMatrixTrace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → Matrix (Fin Nc) (Fin Nc) ℂ) (x : E)
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => Matrix.trace (f y)) x := by
  simp only [Matrix.trace]
  exact Finset.analyticAt_fun_sum Finset.univ (fun i _ => by
    have he := (complexMatrixEntryCLM i i).analyticAt (f x)
    simpa only [Function.comp_apply] using he.comp (f := f) hf)

theorem analyticAt_complexWilsonPlaquetteAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) :
    AnalyticAt ℂ (fun W => complexWilsonPlaquetteAction U W p) Z := by
  exact analyticAt_const.sub
    (analyticAt_complexMatrixTrace _ Z
      (analyticAt_complexWilsonPlaquetteHolonomy U Z p))

/-- On the real center slice, the real part of the holomorphic action is the
literal real Wilson plaquette action. -/
@[simp] theorem complexWilsonPlaquetteAction_zero_re
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    (complexWilsonPlaquetteAction U 0 p).re =
      ambientWilsonPlaquetteAction U 0 p := by
  simp [complexWilsonPlaquetteAction, ambientWilsonPlaquetteAction,
    ambientTraceReal_eq]

/-- Literal finite holomorphic Wilson action on the complex contour chart. -/
def complexWilsonAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc) : ℂ :=
  ∑ p : ConcretePlaquette d N, complexWilsonPlaquetteAction U Z p

theorem analyticAt_complexWilsonAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc) :
    AnalyticAt ℂ (complexWilsonAction U) Z := by
  exact Finset.analyticAt_fun_sum Finset.univ
    (fun p _ => analyticAt_complexWilsonPlaquetteAction U Z p)

/-- The complete finite action has the same center-slice compatibility. -/
@[simp] theorem complexWilsonAction_zero_re
    (U : PhysicalGaugeBackground d N Nc) :
    (complexWilsonAction U 0).re = ambientWilsonAction U 0 := by
  simp [complexWilsonAction, ambientWilsonAction]

/-- Complex Fréchet Hessian evaluated at an arbitrary contour background. -/
def complexWilsonHessianAt
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc) :
    PhysicalComplexMatrixTangent d N Nc →L[ℂ]
      PhysicalComplexMatrixTangent d N Nc →L[ℂ] ℂ :=
  fderiv ℂ (fderiv ℂ (complexWilsonAction U)) Z

/-- The holomorphic Wilson Hessian is symmetric. -/
theorem complexWilsonHessianAt_symm
    (U : PhysicalGaugeBackground d N Nc)
    (Z X Y : PhysicalComplexMatrixTangent d N Nc) :
    complexWilsonHessianAt U Z X Y =
      complexWilsonHessianAt U Z Y X := by
  have hc : ContDiffAt ℂ (2 : WithTop ℕ∞) (complexWilsonAction U) Z :=
    (analyticAt_complexWilsonAction U Z).contDiffAt
  have hs : IsSymmSndFDerivAt ℂ (complexWilsonAction U) Z :=
    hc.isSymmSndFDerivAt (by norm_num [minSmoothness])
  simpa only [complexWilsonHessianAt] using hs.eq X Y

/-- Canonical matrix representative of one real `su(Nc)` basis vector,
viewed in the complexified tangent space. -/
def complexWilsonLieBasisMatrix
    (a : Fin (Nc ^ 2 - 1)) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((suLieCoordIso Nc).symm
    (PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars
      (fun j => if j = a then 1 else 0))).toMatrix

/-- Coordinate basis vector in the complexified physical tangent space. -/
def complexWilsonPhysicalBasisTangent
    (q : PhysicalGaugeCoordIndex d N Nc) :
    PhysicalComplexMatrixTangent d N Nc :=
  fun b => if b = q.1 then complexWilsonLieBasisMatrix q.2 else 0

/-- Literal finite matrix of the holomorphic Wilson Hessian at contour
background `Z`. -/
def complexPhysicalWilsonHessianMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc) :
    Matrix (PhysicalGaugeCoordIndex d N Nc)
      (PhysicalGaugeCoordIndex d N Nc) ℂ :=
  fun i j =>
    complexWilsonHessianAt U Z
      (complexWilsonPhysicalBasisTangent i)
      (complexWilsonPhysicalBasisTangent j)

theorem complexPhysicalWilsonHessianMatrix_transpose
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalComplexMatrixTangent d N Nc) :
    (complexPhysicalWilsonHessianMatrix U Z)ᵀ =
      complexPhysicalWilsonHessianMatrix U Z := by
  ext i j
  exact complexWilsonHessianAt_symm U Z _ _

end

end YangMills.RG
