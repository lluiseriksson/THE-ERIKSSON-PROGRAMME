import YangMills.RG.BalabanCMP116FourFactorSecondDerivative
import YangMills.RG.BalabanCMP116WilsonHessianFlatDictionary

/-!
# Exact oriented-edge variations at an arbitrary Wilson background

For a positive physical bond with generator `X`, the ambient chart is
`exp(tX) U`.  The reverse orientation is
`(exp(tX) U)ᴴ = Uᴴ exp(-tX)`.  This module records the two cases in a single
ordered-factor interface and proves their first and second derivatives.

The signs and multiplication sides are fixed here before any plaquette
estimate is attempted.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The positive-bond background matrix underlying an oriented edge. -/
def orientedWilsonPositiveBase
    (U : PhysicalGaugeBackground d N Nc) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))).val

/-- The signed `su(N)` generator attached to an oriented edge. -/
def orientedWilsonGenerator
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  flatOrientedSuMatrixTangent A e

/-- Ordered model for the varied oriented edge.

Positive orientations multiply the fixed background on the right.  Negative
orientations multiply the exponential increment on the right of `Uᴴ`.
-/
def orientedWilsonFactor
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    physicalMatrixExp (t • orientedWilsonGenerator A e) *
      orientedWilsonPositiveBase U e
  else
    (orientedWilsonPositiveBase U e)ᴴ *
      physicalMatrixExp (t • orientedWilsonGenerator A e)

/-- First-variation curve of `orientedWilsonFactor`. -/
def orientedWilsonFactorFirst
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    (physicalMatrixExp (t • orientedWilsonGenerator A e) *
      orientedWilsonGenerator A e) * orientedWilsonPositiveBase U e
  else
    (orientedWilsonPositiveBase U e)ᴴ *
      (physicalMatrixExp (t • orientedWilsonGenerator A e) *
        orientedWilsonGenerator A e)

/-- Second-variation value of one oriented factor at time `t`. -/
def orientedWilsonFactorSecond
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    ((physicalMatrixExp (t • orientedWilsonGenerator A e) *
      orientedWilsonGenerator A e) * orientedWilsonGenerator A e) *
        orientedWilsonPositiveBase U e
  else
    (orientedWilsonPositiveBase U e)ᴴ *
      ((physicalMatrixExp (t • orientedWilsonGenerator A e) *
        orientedWilsonGenerator A e) * orientedWilsonGenerator A e)

/-- The literal ambient-chart edge curve equals the ordered model above. -/
theorem ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    ambientOrientedEdgeMatrix U
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) e =
      orientedWilsonFactor U A e t := by
  rcases e with ⟨x, i, sign⟩
  cases sign
  · simp only [ambientOrientedEdgeMatrix, Bool.false_eq_true, if_false,
      ambientPositiveBondMatrix, physicalSuTangentToAmbient,
      physicalCochainToSuMatrixTangent, Pi.smul_apply,
      orientedWilsonFactor, orientedWilsonGenerator,
      orientedWilsonPositiveBase, flatOrientedSuMatrixTangent,
      physicalBondOfEdge]
    rw [Matrix.conjTranspose_mul, physicalMatrixExp_conjTranspose]
    have hskew :
        (((suLieCoordIso Nc).symm (A (x, i))).toMatrix)ᴴ =
          -((suLieCoordIso Nc).symm (A (x, i))).toMatrix := by
      exact (mem_suMatrixSubmodule_iff
        (((suLieCoordIso Nc).symm (A (x, i))).toMatrix)).mp
          (((suLieCoordIso Nc).symm (A (x, i))).property) |>.1
    rw [Matrix.conjTranspose_smul, star_trivial, hskew]
  · simp [ambientOrientedEdgeMatrix, ambientPositiveBondMatrix,
      physicalSuTangentToAmbient, physicalCochainToSuMatrixTangent,
      orientedWilsonFactor, orientedWilsonGenerator,
      orientedWilsonPositiveBase, flatOrientedSuMatrixTangent]

/-- Exact first derivative of one oriented Wilson factor. -/
theorem hasDerivAt_orientedWilsonFactor
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    HasDerivAt (orientedWilsonFactor U A e)
      (orientedWilsonFactorFirst U A e t) t := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let X := orientedWilsonGenerator A e
  have hExp : HasDerivAt
      (fun u : ℝ => physicalMatrixExp (u • X))
      (physicalMatrixExp (t • X) * X) t := by
    simpa [physicalMatrixExp] using hasDerivAt_exp_smul_const X t
  cases h : e.sign
  · have hfun : orientedWilsonFactor U A e =
        fun u => (orientedWilsonPositiveBase U e)ᴴ *
          physicalMatrixExp (u • orientedWilsonGenerator A e) := by
      funext u
      simp only [orientedWilsonFactor, h, Bool.false_eq_true, if_false]
    rw [hfun]
    simpa only [orientedWilsonFactorFirst, h, Bool.false_eq_true, if_false, X] using
      hExp.const_mul ((orientedWilsonPositiveBase U e)ᴴ)
  · have hfun : orientedWilsonFactor U A e =
        fun u => physicalMatrixExp (u • orientedWilsonGenerator A e) *
          orientedWilsonPositiveBase U e := by
      funext u
      simp only [orientedWilsonFactor, h, if_true]
    rw [hfun]
    simpa only [orientedWilsonFactorFirst, h, if_true, X] using
      hExp.mul_const (orientedWilsonPositiveBase U e)

/-- Exact second derivative of one oriented Wilson factor. -/
theorem hasDerivAt_orientedWilsonFactorFirst
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    HasDerivAt (orientedWilsonFactorFirst U A e)
      (orientedWilsonFactorSecond U A e t) t := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let X := orientedWilsonGenerator A e
  have hExp : HasDerivAt
      (fun u : ℝ => physicalMatrixExp (u • X))
      (physicalMatrixExp (t • X) * X) t := by
    simpa [physicalMatrixExp] using hasDerivAt_exp_smul_const X t
  have hExpX : HasDerivAt
      (fun u : ℝ => physicalMatrixExp (u • X) * X)
      ((physicalMatrixExp (t • X) * X) * X) t :=
    hExp.mul_const X
  cases h : e.sign
  · have hfun : orientedWilsonFactorFirst U A e =
        fun u => (orientedWilsonPositiveBase U e)ᴴ *
          (physicalMatrixExp (u • orientedWilsonGenerator A e) *
            orientedWilsonGenerator A e) := by
      funext u
      simp only [orientedWilsonFactorFirst, h, Bool.false_eq_true, if_false]
    rw [hfun]
    simpa only [orientedWilsonFactorSecond, h, Bool.false_eq_true, if_false, X] using
      hExpX.const_mul ((orientedWilsonPositiveBase U e)ᴴ)
  · have hfun : orientedWilsonFactorFirst U A e =
        fun u => (physicalMatrixExp (u • orientedWilsonGenerator A e) *
          orientedWilsonGenerator A e) * orientedWilsonPositiveBase U e := by
      funext u
      simp only [orientedWilsonFactorFirst, h, if_true]
    rw [hfun]
    simpa only [orientedWilsonFactorSecond, h, if_true, X] using
      hExpX.mul_const (orientedWilsonPositiveBase U e)

@[simp]
theorem orientedWilsonFactor_zero
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactor U A e 0 =
      ambientOrientedEdgeMatrix U 0 e := by
  have h :=
    (ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor U A e 0).symm
  have hz :
      (0 : ℝ) • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A) =
        (0 : PhysicalAmbientMatrixTangent d N Nc) :=
    zero_smul ℝ _
  rw [hz] at h
  exact h

/-- The literal plaquette line is the ordered product of the four exact
oriented-factor curves. -/
theorem ambientPlaquetteHolonomy_line_eq_fourFactorProduct
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) :
    ambientPlaquetteHolonomy U
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) p =
      fourFactorProduct
        (fun k => orientedWilsonFactor U A (p.edges k)) t := by
  unfold ambientPlaquetteHolonomy fourFactorProduct
  rw [ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor,
    ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor,
    ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor,
    ambientOrientedEdgeMatrix_line_eq_orientedWilsonFactor]

end

end YangMills.RG
