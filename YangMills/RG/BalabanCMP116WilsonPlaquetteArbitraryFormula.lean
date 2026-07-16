import YangMills.RG.BalabanCMP116WilsonOrientedEdgeVariation
import YangMills.RG.BalabanCMP116WilsonHessianFlatPlaquette

/-!
# Exact local Wilson Hessian formula at an arbitrary background

This module combines the ordered four-factor product rule with the exact
positive/negative edge variations.  The result is a literal formula for the
quadratic local Hessian of one plaquette at any physical background.

No small-background or Lipschitz estimate is assumed here.  The formula is
the algebraic input from which those estimates must be proved.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The four background factor values around a plaquette. -/
def orientedPlaquetteFactorValue
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  orientedWilsonFactor U A (p.edges k) 0

/-- The four first edge variations around a plaquette. -/
def orientedPlaquetteFactorFirst
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  orientedWilsonFactorFirst U A (p.edges k) 0

/-- The four second edge variations around a plaquette. -/
def orientedPlaquetteFactorSecond
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  orientedWilsonFactorSecond U A (p.edges k) 0

/-- Fully expanded ordered second variation of one plaquette holonomy. -/
def orientedPlaquetteHolonomySecondVariation
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorSecond
    (orientedPlaquetteFactorValue U A p)
    (orientedPlaquetteFactorFirst U A p)
    (orientedPlaquetteFactorSecond U A p)

/-- Scalar quadratic formula for the local Wilson Hessian. -/
def orientedWilsonPlaquetteQuadraticFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  -ambientTraceReal (orientedPlaquetteHolonomySecondVariation U A p)

/-- Polarized mixed formula obtained from the exact quadratic expression. -/
def orientedWilsonPlaquetteMixedFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  (orientedWilsonPlaquetteQuadraticFormula U (A + B) p -
      orientedWilsonPlaquetteQuadraticFormula U A p -
      orientedWilsonPlaquetteQuadraticFormula U B p) / 2

/-- The exact four-factor representation of the local Wilson action line. -/
def orientedWilsonPlaquetteActionLine
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) : ℝ :=
  1 - ambientTraceReal
    (fourFactorProduct
      (fun k => orientedWilsonFactor U A (p.edges k)) t)

theorem ambientWilsonPlaquetteAction_line_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) :
    ambientWilsonPlaquetteAction U
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) p =
      orientedWilsonPlaquetteActionLine U A p t := by
  unfold ambientWilsonPlaquetteAction orientedWilsonPlaquetteActionLine
  rw [ambientPlaquetteHolonomy_line_eq_fourFactorProduct]

/-- First derivative of the arbitrary-background local action line. -/
theorem hasDerivAt_orientedWilsonPlaquetteActionLine
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) :
    HasDerivAt (orientedWilsonPlaquetteActionLine U A p)
      (-ambientTraceReal
        (fourFactorFirst
          (fun k => orientedWilsonFactor U A (p.edges k))
          (fun k => orientedWilsonFactorFirst U A (p.edges k)) t)) t := by
  let F := fun k : Fin 4 => orientedWilsonFactor U A (p.edges k)
  let dF := fun k : Fin 4 => orientedWilsonFactorFirst U A (p.edges k)
  have hprod : HasDerivAt (fourFactorProduct F)
      (fourFactorFirst F dF t) t :=
    hasDerivAt_fourFactorProduct F dF t
      (fun k => hasDerivAt_orientedWilsonFactor U A (p.edges k) t)
  have htraceRaw :=
    (fourFactorTraceRealCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt t hprod
  have htrace : HasDerivAt
      (fun u => ambientTraceReal (fourFactorProduct F u))
      (ambientTraceReal (fourFactorFirst F dF t)) t := by
    convert htraceRaw using 1
    · funext u
      exact (fourFactorTraceRealCLM_apply (fourFactorProduct F u)).symm
    · exact (fourFactorTraceRealCLM_apply (fourFactorFirst F dF t)).symm
  simpa only [orientedWilsonPlaquetteActionLine, F, dF] using
    htrace.const_sub (1 : ℝ)

/-- Exact second derivative of the arbitrary-background local action line. -/
theorem secondDeriv_orientedWilsonPlaquetteActionLine_zero
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    deriv
      (fun t => deriv (orientedWilsonPlaquetteActionLine U A p) t) 0 =
      orientedWilsonPlaquetteQuadraticFormula U A p := by
  let F := fun k : Fin 4 => orientedWilsonFactor U A (p.edges k)
  let dF := fun k : Fin 4 => orientedWilsonFactorFirst U A (p.edges k)
  let Y := fun k : Fin 4 => orientedWilsonFactorSecond U A (p.edges k) 0
  have hfirst :
      (fun t => deriv (orientedWilsonPlaquetteActionLine U A p) t) =
        fun t => -ambientTraceReal (fourFactorFirst F dF t) := by
    funext t
    exact (hasDerivAt_orientedWilsonPlaquetteActionLine U A p t).deriv
  rw [hfirst]
  have hsecond : HasDerivAt
      (fun t => -ambientTraceReal (fourFactorFirst F dF t))
      (-ambientTraceReal
        (fourFactorSecond (fun k => F k 0) (fun k => dF k 0) Y)) 0 := by
    exact (hasDerivAt_traceReal_fourFactorFirst F dF Y 0
      (fun k => hasDerivAt_orientedWilsonFactor U A (p.edges k) 0)
      (fun k => hasDerivAt_orientedWilsonFactorFirst U A (p.edges k) 0)).neg
  change deriv (fun t => -ambientTraceReal (fourFactorFirst F dF t)) 0 =
    orientedWilsonPlaquetteQuadraticFormula U A p
  rw [hsecond.deriv]
  rfl

/-- The literal Fréchet local Hessian on a repeated physical direction is
exactly the expanded ordered plaquette formula. -/
theorem ambientWilsonPlaquetteHessian_self_eq_arbitraryFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      orientedWilsonPlaquetteQuadraticFormula U A p := by
  let X := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent A)
  let f := fun Z : PhysicalAmbientMatrixTangent d N Nc =>
    ambientWilsonPlaquetteAction U Z p
  have hsnd := secondDeriv_line_eq_sndFDeriv f
    (fun Z => analyticAt_ambientWilsonPlaquetteAction U Z p) X
  have hcurve :
      (fun t : ℝ => f (t • X)) =
        orientedWilsonPlaquetteActionLine U A p := by
    funext t
    exact ambientWilsonPlaquetteAction_line_eq U A p t
  change ((fderiv ℝ (fderiv ℝ f) 0) X) X =
    orientedWilsonPlaquetteQuadraticFormula U A p
  rw [← hsnd]
  have hderiv :
      (fun t => deriv (fun s => f (s • X)) t) =
        fun t => deriv (orientedWilsonPlaquetteActionLine U A p) t := by
    funext t
    rw [hcurve]
  have hout :
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (s • X)) t) (0 : ℝ) =
        deriv
          (fun t : ℝ =>
            deriv (orientedWilsonPlaquetteActionLine U A p) t) (0 : ℝ) :=
    congrArg (fun g : ℝ → ℝ => deriv g 0) hderiv
  exact hout.trans
    (secondDeriv_orientedWilsonPlaquetteActionLine_zero U A p)

/-- The mixed local Hessian is the polarization of the explicit arbitrary-
background quadratic formula. -/
theorem ambientWilsonPlaquetteHessian_eq_arbitraryMixedFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) =
      orientedWilsonPlaquetteMixedFormula U A B p := by
  let XA := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent A)
  let XB := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent B)
  rw [orientedWilsonPlaquetteMixedFormula]
  rw [← ambientWilsonPlaquetteHessian_self_eq_arbitraryFormula U (A + B) p,
    ← ambientWilsonPlaquetteHessian_self_eq_arbitraryFormula U A p,
    ← ambientWilsonPlaquetteHessian_self_eq_arbitraryFormula U B p]
  rw [physicalCochainToAmbient_add]
  change ambientWilsonPlaquetteHessian U p XA XB =
    (ambientWilsonPlaquetteHessian U p (XA + XB) (XA + XB) -
      ambientWilsonPlaquetteHessian U p XA XA -
      ambientWilsonPlaquetteHessian U p XB XB) / 2
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [ambientWilsonPlaquetteHessian_symm U p XB XA]
  ring

end

end YangMills.RG
