import YangMills.RG.BalabanCMP116FourFactorMixed
import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds
import YangMills.RG.BalabanCMP116WilsonHessianFlatPlaquette

/-!
# Direct mixed variation of one oriented Wilson factor

For the exponential chart `exp(tX + sY)`, the mixed derivative at the
origin is `(XY + YX) / 2`.  This module places that symmetric product on the
correct side of the fixed background matrix for each edge orientation and
connects it exactly with polarization of the existing one-parameter second
variation.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Linearity of the signed oriented generator in the physical cochain. -/
theorem orientedWilsonGenerator_add
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonGenerator (A + B) e =
      orientedWilsonGenerator A e + orientedWilsonGenerator B e := by
  exact flatOrientedSuMatrixTangent_add A B e

/-- The zero scalar line evaluates the matrix exponential at the identity. -/
@[simp]
theorem physicalMatrixExp_zero_smul
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    physicalMatrixExp ((0 : ℝ) • X) = 1 := by
  have hz : (0 : ℝ) • X = (0 : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    ext i j
    simp
  rw [hz]
  exact physicalMatrixExp_zero

/-- Numerator of the direct mixed second variation of one oriented edge.

Polarization of `X ↦ X²` gives the ordered sum `XY + YX`.
-/
def orientedWilsonFactorMixedNumerator
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  let mixed :=
    orientedWilsonGenerator A e * orientedWilsonGenerator B e +
      orientedWilsonGenerator B e * orientedWilsonGenerator A e
  if e.sign then
    mixed * orientedWilsonPositiveBase U e
  else
    (orientedWilsonPositiveBase U e)ᴴ * mixed

/-- Direct mixed second variation of one oriented edge factor at the origin. -/
def orientedWilsonFactorMixedSecond
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (2 : ℝ)⁻¹ • orientedWilsonFactorMixedNumerator U A B e

/-- The zero-time factor is the orientation-independent background factor. -/
theorem orientedWilsonFactor_zero_eq_background
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactor U A e 0 =
      orientedWilsonBackgroundFactor U e := by
  cases h : e.sign
  · simp [orientedWilsonFactor, orientedWilsonBackgroundFactor, h,
      physicalMatrixExp_zero_smul]
  · simp [orientedWilsonFactor, orientedWilsonBackgroundFactor, h,
      physicalMatrixExp_zero_smul]

/-- The first variation at zero is additive in the physical direction. -/
theorem orientedWilsonFactorFirst_zero_add
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactorFirst U (A + B) e 0 =
      orientedWilsonFactorFirst U A e 0 +
        orientedWilsonFactorFirst U B e 0 := by
  cases h : e.sign
  · simp only [orientedWilsonFactorFirst, h, Bool.false_eq_true, if_false,
      physicalMatrixExp_zero_smul, one_mul, orientedWilsonGenerator_add]
    noncomm_ring
  · simp only [orientedWilsonFactorFirst, h, if_true, zero_smul,
      physicalMatrixExp_zero_smul, one_mul, orientedWilsonGenerator_add]
    noncomm_ring

/-- The numerator is exactly the polarization cross term of the existing
one-parameter second variation. -/
theorem orientedWilsonFactorMixedNumerator_eq_polarization
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactorMixedNumerator U A B e =
      orientedWilsonFactorSecond U (A + B) e 0 -
        orientedWilsonFactorSecond U A e 0 -
        orientedWilsonFactorSecond U B e 0 := by
  cases h : e.sign
  · simp only [orientedWilsonFactorMixedNumerator, h, Bool.false_eq_true,
      if_false, orientedWilsonFactorSecond, zero_smul,
      physicalMatrixExp_zero_smul, one_mul, orientedWilsonGenerator_add]
    noncomm_ring
  · simp only [orientedWilsonFactorMixedNumerator, h, if_true,
      orientedWilsonFactorSecond, zero_smul, physicalMatrixExp_zero_smul, one_mul,
      orientedWilsonGenerator_add]
    noncomm_ring

/-- The direct mixed edge formula is exactly half the polarization cross
term. -/
theorem two_smul_orientedWilsonFactorMixedSecond_eq_polarization
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    2 • orientedWilsonFactorMixedSecond U A B e =
      orientedWilsonFactorSecond U (A + B) e 0 -
        orientedWilsonFactorSecond U A e 0 -
        orientedWilsonFactorSecond U B e 0 := by
  rw [orientedWilsonFactorMixedSecond,
    orientedWilsonFactorMixedNumerator_eq_polarization]
  module

end

end YangMills.RG
