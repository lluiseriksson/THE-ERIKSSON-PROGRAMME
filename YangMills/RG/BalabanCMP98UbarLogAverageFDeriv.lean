/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP116WilsonHessianDifferential
import YangMills.RG.NearLogWeightedFDeriv
import YangMills.RG.Ubar

/-!
# The literal CMP98 logarithmic block average in the ambient matrix chart

CMP98 (121)--(124) differentiates the logarithm of the nonlinear block
average at a nontrivial background.  This file constructs the matrix-valued
function that is actually differentiated.  For every fine point in the
source block it uses the three literal CMP99 contours and the inverse of the
straight coarse-bond transport, hence the local deviation is

`W₁(Z) * W₂(Z) * W₃(Z) * W₄(Z)ᴴ - 1`.

The conjugate transpose is the analytic ambient extension of the inverse on
the physical unitary chart.  The terminal theorem differentiates the finite
block sum by the complete ordered Mercator derivative.  It does not identify
that derivative with the shorter main term `Q₀` of CMP98 (125), and it does
not discard the three noncommutative correction terms of (124).
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98MatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one]
    rw [Matrix.l2_opNorm_diagonal]
    simp

/-- Ordered matrix holonomy of a literal oriented path in the ambient
exponential chart. -/
def cmp98AmbientWilsonLineMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    List (ConcreteEdge d (M * N')) → Matrix (Fin Nc) (Fin Nc) ℂ
  | [] => 1
  | e :: es => ambientOrientedEdgeMatrix U Z e *
      cmp98AmbientWilsonLineMatrix U Z es

@[simp] theorem cmp98AmbientWilsonLineMatrix_nil
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    cmp98AmbientWilsonLineMatrix U Z [] = 1 := rfl

@[simp] theorem cmp98AmbientWilsonLineMatrix_cons
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (e : ConcreteEdge d (M * N'))
    (es : List (ConcreteEdge d (M * N'))) :
    cmp98AmbientWilsonLineMatrix U Z (e :: es) =
      ambientOrientedEdgeMatrix U Z e *
        cmp98AmbientWilsonLineMatrix U Z es := rfl

/-- Every finite contour holonomy is analytic in the ambient matrix chart. -/
theorem analyticAt_cmp98AmbientWilsonLineMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    AnalyticAt ℝ (fun W => cmp98AmbientWilsonLineMatrix U W es) Z := by
  induction es with
  | nil =>
      simp only [cmp98AmbientWilsonLineMatrix_nil]
      exact analyticAt_const
  | cons e es ih =>
      simp only [cmp98AmbientWilsonLineMatrix_cons]
      exact (analyticAt_ambientOrientedEdgeMatrix U Z e).mul ih

/-- On genuine `su(N)` directions, the ambient ordered product is literally
the matrix underlying the physical unitary Wilson line. -/
theorem cmp98AmbientWilsonLineMatrix_twoParameter_eq_unitaryWilsonLine
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (X Y : PhysicalSuMatrixTangent d (M * N') Nc)
    (t s : ℝ) (es : List (ConcreteEdge d (M * N'))) :
    cmp98AmbientWilsonLineMatrix U
        (physicalTwoParameterAmbientTangent X Y t s) es =
      (wilsonLine (physicalSuUnitaryLeftVariation U X Y t s) es : UN Nc).val := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      rw [cmp98AmbientWilsonLineMatrix_cons, wilsonLine_cons,
        ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation U X Y e t s,
        ih]
      rfl

/-- The straight basepoint-to-basepoint transport representing the coarse
bond `U(c)` in CMP98/CMP99. -/
def cmp98SourceCoarseBondPath (b : PhysicalBond d N') :
    List (ConcreteEdge d (M * N')) :=
  (cmp99SourceParallelTransportPath (G := SUN Nc)
    (blockBasepoint M N' b.1) b.2).edges

/-- Literal local matrix deviation entering the logarithm in CMP98 (121).
The fourth factor is conjugate transpose, hence exactly inverse on the
physical unitary chart while remaining analytic on the ambient chart. -/
def cmp98UbarAmbientDeviationMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((cmp98AmbientWilsonLineMatrix U Z
        (cmp99SourceUbarGamma1 (G := SUN Nc) b x) *
      cmp98AmbientWilsonLineMatrix U Z
        (cmp99SourceUbarGamma2 (G := SUN Nc) b x)) *
    cmp98AmbientWilsonLineMatrix U Z
      (cmp99SourceUbarGamma3 (G := SUN Nc) b x)) *
      (cmp98AmbientWilsonLineMatrix U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b))ᴴ - 1

/-- Analyticity of the complete four-contour deviation, rather than of an
arbitrary replacement map. -/
theorem analyticAt_cmp98UbarAmbientDeviationMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    AnalyticAt ℝ
      (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z := by
  have h1 := analyticAt_cmp98AmbientWilsonLineMatrix U Z
    (cmp99SourceUbarGamma1 (G := SUN Nc) b x)
  have h2 := analyticAt_cmp98AmbientWilsonLineMatrix U Z
    (cmp99SourceUbarGamma2 (G := SUN Nc) b x)
  have h3 := analyticAt_cmp98AmbientWilsonLineMatrix U Z
    (cmp99SourceUbarGamma3 (G := SUN Nc) b x)
  have h4 := analyticAt_cmp98AmbientWilsonLineMatrix U Z
    (cmp98SourceCoarseBondPath (Nc := Nc) b)
  have hstar : AnalyticAt ℝ
      (fun W => (cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceCoarseBondPath (Nc := Nc) b))ᴴ) Z := by
    have hout : AnalyticAt ℝ
        (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => Aᴴ)
        (cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) b)) := by
      simpa only [matrixConjTransposeCLM_apply] using
        matrixConjTransposeCLM.analyticAt
          (cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b))
    simpa only [Function.comp_apply] using
      hout.comp
        (f := fun W => cmp98AmbientWilsonLineMatrix U W
          (cmp98SourceCoarseBondPath (Nc := Nc) b)) h4
  exact (((h1.mul h2).mul h3).mul hstar).sub analyticAt_const

/-- The logarithmic exponent of the nonlinear block average.  This is the
finite expression whose derivative gives the complete CMP98 block operator,
before the conventional Lie-coordinate normalization. -/
def cmp98UbarLogAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((M : ℝ) ^ d)⁻¹ •
    ∑ x ∈ blockOf M N' b.1,
      nearLog (cmp98UbarAmbientDeviationMatrix U b x Z)

/-- Exact Fréchet derivative of the literal finite CMP98 logarithmic
average at a nontrivial near-identity background.  Each summand uses the
ordered Mercator derivative composed with the derivative of the physical
four-contour deviation. -/
theorem hasFDerivAt_cmp98UbarLogAverage
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    HasFDerivAt (cmp98UbarLogAverage U b)
      (((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          ((∑' n : ℕ,
              nearLogTermFDeriv
                (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
            (fderiv ℝ
              (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z))) Z := by
  have hlocal : ∀ x ∈ blockOf M N' b.1,
      HasFDerivAt
        (fun W => nearLog (cmp98UbarAmbientDeviationMatrix U b x W))
        ((∑' n : ℕ,
            nearLogTermFDeriv
              (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
          (fderiv ℝ
            (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z)) Z := by
    intro x hx
    exact HasFDerivAt.nearLog_of_norm_lt_one
      ((analyticAt_cmp98UbarAmbientDeviationMatrix U b x Z).differentiableAt.hasFDerivAt)
      (hsmall x hx)
  have hsum := HasFDerivAt.fun_sum hlocal
  simpa only [cmp98UbarLogAverage] using
    hsum.const_smul (((M : ℝ) ^ d)⁻¹)

end

end YangMills.RG
