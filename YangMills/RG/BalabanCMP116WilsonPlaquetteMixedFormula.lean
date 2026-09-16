import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixed
import YangMills.RG.BalabanCMP116WilsonPlaquetteArbitraryFormula

/-!
# Direct mixed Wilson plaquette formula

This module inserts the direct mixed variation of each oriented edge into the
ordered four-factor product rule.  The resulting sixteen-term matrix formula
is proved equal to the polarization of the exact arbitrary-background
quadratic formula, and hence to the literal mixed Wilson Hessian.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Direct mixed second variations of the four oriented edge factors. -/
def orientedPlaquetteFactorMixedSecond
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  orientedWilsonFactorMixedSecond U A B (p.edges k)

/-- Direct sixteen-term mixed variation of one plaquette holonomy. -/
def orientedPlaquetteHolonomyMixedVariation
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  fourFactorMixed
    (fun k => orientedWilsonBackgroundFactor U (p.edges k))
    (orientedPlaquetteFactorFirst U A p)
    (orientedPlaquetteFactorFirst U B p)
    (orientedPlaquetteFactorMixedSecond U A B p)

/-- Direct scalar mixed formula for the local Wilson Hessian. -/
def orientedWilsonPlaquetteDirectMixedFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  -ambientTraceReal
    (orientedPlaquetteHolonomyMixedVariation U A B p)

/-- The direct mixed holonomy formula is exactly half the polarization of
the three quadratic holonomy variations. -/
theorem two_smul_orientedPlaquetteHolonomyMixedVariation_eq_polarization
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    2 • orientedPlaquetteHolonomyMixedVariation U A B p =
      orientedPlaquetteHolonomySecondVariation U (A + B) p -
        orientedPlaquetteHolonomySecondVariation U A p -
        orientedPlaquetteHolonomySecondVariation U B p := by
  let W := fun k : Fin 4 =>
    orientedWilsonBackgroundFactor U (p.edges k)
  let XA := orientedPlaquetteFactorFirst U A p
  let XB := orientedPlaquetteFactorFirst U B p
  let YA := orientedPlaquetteFactorSecond U A p
  let YB := orientedPlaquetteFactorSecond U B p
  let YAB := orientedPlaquetteFactorMixedSecond U A B p
  have hW (C : PhysicalGaugeOneCochain d N Nc) :
      orientedPlaquetteFactorValue U C p = W := by
    funext k
    exact orientedWilsonFactor_zero_eq_background U C (p.edges k)
  have hX :
      orientedPlaquetteFactorFirst U (A + B) p = XA + XB := by
    funext k
    exact orientedWilsonFactorFirst_zero_add U A B (p.edges k)
  have hY :
      orientedPlaquetteFactorSecond U (A + B) p =
        YA + YB + 2 • YAB := by
    funext k
    have hk :=
      two_smul_orientedWilsonFactorMixedSecond_eq_polarization
        U A B (p.edges k)
    change orientedWilsonFactorSecond U (A + B) (p.edges k) 0 =
      orientedWilsonFactorSecond U A (p.edges k) 0 +
        orientedWilsonFactorSecond U B (p.edges k) 0 +
        2 • orientedWilsonFactorMixedSecond U A B (p.edges k)
    rw [hk]
    module
  have hfour :=
    two_smul_fourFactorMixed_eq_polarization W XA XB YA YB YAB
  simpa only [orientedPlaquetteHolonomyMixedVariation,
    orientedPlaquetteHolonomySecondVariation, hW, hX, hY, W, XA, XB, YA,
    YB, YAB] using hfour

/-- The direct scalar formula equals the polarized scalar formula. -/
theorem orientedWilsonPlaquetteDirectMixedFormula_eq_mixedFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    orientedWilsonPlaquetteDirectMixedFormula U A B p =
      orientedWilsonPlaquetteMixedFormula U A B p := by
  have hmatrix :=
    two_smul_orientedPlaquetteHolonomyMixedVariation_eq_polarization
      U A B p
  have htrace :=
    congrArg (fourFactorTraceRealCLM (Nc := Nc)) hmatrix
  simp only [map_nsmul, map_sub, fourFactorTraceRealCLM_apply] at htrace
  unfold orientedWilsonPlaquetteDirectMixedFormula
    orientedWilsonPlaquetteMixedFormula
    orientedWilsonPlaquetteQuadraticFormula
  norm_num [two_nsmul] at htrace ⊢
  linarith

/-- The literal mixed local Hessian is the direct sixteen-term plaquette
formula. -/
theorem ambientWilsonPlaquetteHessian_eq_directMixedFormula
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) =
      orientedWilsonPlaquetteDirectMixedFormula U A B p := by
  rw [ambientWilsonPlaquetteHessian_eq_arbitraryMixedFormula,
    orientedWilsonPlaquetteDirectMixedFormula_eq_mixedFormula]

end

end YangMills.RG
