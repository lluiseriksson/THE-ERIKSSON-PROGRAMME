import YangMills.SU2ThetaPrism.Representation
import YangMills.SU2ThetaPrism.Analysis

/-!
# Character coefficients, central multipliers, and the fixed beta gate
-/

noncomputable section

open MeasureTheory

namespace YangMills.SU2ThetaPrism

/-- The fabrication domain is exactly `0 < beta <= 1`. -/
def BetaDomain (beta : ℝ) : Prop :=
  0 < beta ∧ beta ≤ 1

theorem one_mem_betaDomain : BetaDomain 1 := by
  constructor <;> norm_num

/-- Real-valued probes indexed by twice-spin.  The abstract coefficient lemma
uses this neutral function-space name; the front door below instantiates it
with `su2WeylPolynomial`, whose low-spin entries have explicit
representation-ring bridges. -/
abbrev RealProbeFamily := TwiceSpin → SU2 → ℝ

/-- The concrete low-spin SU(2) Weyl polynomials consumed by this gate.
Only labels `1` (spin one-half) and `2` (spin one) occur in the endpoint. -/
def su2WeylPolynomial : RealProbeFamily
  | 1, g => (chi g).re
  | 2, g => (chi g).re ^ 2 - 1
  | _, _ => 0

@[simp] theorem su2WeylPolynomial_spinHalf (g : SU2) :
    su2WeylPolynomial 1 g = (chi g).re := rfl

@[simp] theorem su2WeylPolynomial_spinOne (g : SU2) :
    su2WeylPolynomial 2 g = (chi g).re ^ 2 - 1 := rfl

/-- The label-one probe is literally the character of the constructed
fundamental continuous unitary representation. -/
theorem su2WeylPolynomial_spinHalf_representation_bridge (g : SU2) :
    (su2WeylPolynomial 1 g : ℂ) =
      YangMills.ClayCore.ContinuousUnitaryMatrixRep.character fundamentalRep g := by
  rw [YangMills.ClayCore.ContinuousUnitaryMatrixRep.character_apply]
  change ((chi g).re : ℂ) = chi g
  have him : (chi g).im = 0 := by
    have h := congrArg Complex.im (chi_star_eq g)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext <;> simp [him]

/-- Clebsch--Gordan character-ring bridge at the only higher label consumed:
the spin-one Weyl polynomial plus the trivial character is the character of
the tensor square of the constructed fundamental representation.  This avoids
presenting an arbitrary family of functions as representation data. -/
theorem su2WeylPolynomial_spinOne_tensor_square_bridge (g : SU2) :
    (su2WeylPolynomial 2 g : ℂ) + 1 =
      (YangMills.ClayCore.ContinuousUnitaryMatrixRep.character fundamentalRep g) ^ 2 := by
  rw [← su2WeylPolynomial_spinHalf_representation_bridge]
  simp only [su2WeylPolynomial_spinOne, su2WeylPolynomial_spinHalf]
  norm_cast
  ring

/-- Registered coefficient integral. -/
def alpha (characters : RealProbeFamily) (beta : ℝ) (j : TwiceSpin) : ℝ :=
  ∫ g : SU2,
    Real.exp ((beta / 2) * (chi g).re) * characters j g
      ∂haarSU2

/-- Central convolution multiplier `alpha_j/(2j+1)`, with the denominator
derived from the general representation dimension. -/
def centralMultiplier (a : TwiceSpin → ℝ) (j : TwiceSpin) : ℝ :=
  a j / representationDimension j

theorem centralMultiplier_spinHalf (a : TwiceSpin → ℝ) :
    centralMultiplier a 1 = a 1 / 2 := by
  norm_num [centralMultiplier, representationDimension]

theorem centralMultiplier_spinOne (a : TwiceSpin → ℝ) :
    centralMultiplier a 2 = a 2 / 3 := by
  norm_num [centralMultiplier, representationDimension]

/-- Pairing assembled from the witness norm and three central multipliers.
The rational factor is deliberately not part of this definition. -/
def thetaPairingFromMultipliers
    (witnessNormSq : ℝ) (a : TwiceSpin → ℝ) : ℝ :=
  witnessNormSq * centralMultiplier a 2 * (centralMultiplier a 1) ^ 2

/-- `1/16` follows from the independently derived norm and dimensions. -/
theorem thetaPairing_factor_sixteen (a : TwiceSpin → ℝ) :
    thetaPairingFromMultipliers (3 / 4) a = a 2 * (a 1) ^ 2 / 16 := by
  rw [thetaPairingFromMultipliers, centralMultiplier_spinOne,
    centralMultiplier_spinHalf]
  ring

/-- Technical series-remainder inputs on the pre-registered interval.  These
are coefficient lower steps, not the pairing or gate conclusion. -/
structure CoefficientRemainderSteps (a : TwiceSpin → ℝ) (beta : ℝ) : Prop where
  half_remainder_nonnegative : 0 ≤ a 1 - beta / 2
  one_remainder_nonnegative : 0 ≤ a 2 - beta ^ 2 / 8

theorem coefficient_half_lower {a : TwiceSpin → ℝ} {beta : ℝ}
    (steps : CoefficientRemainderSteps a beta) : beta / 2 ≤ a 1 := by
  linarith [steps.half_remainder_nonnegative]

theorem coefficient_one_lower {a : TwiceSpin → ℝ} {beta : ℝ}
    (steps : CoefficientRemainderSteps a beta) : beta ^ 2 / 8 ≤ a 2 := by
  linarith [steps.one_remainder_nonnegative]

/-- Fixed manufactured inequality.  It is local to this artefact and is not
programme Gate 7. -/
theorem thetaPairing_gate {a : TwiceSpin → ℝ} {beta : ℝ}
    (hbeta : BetaDomain beta) (steps : CoefficientRemainderSteps a beta) :
    beta ^ 4 / 512 ≤ thetaPairingFromMultipliers (3 / 4) a := by
  rw [thetaPairing_factor_sixteen]
  have hb0 : 0 ≤ beta / 2 := by linarith [hbeta.1]
  have ha1 : beta / 2 ≤ a 1 := coefficient_half_lower steps
  have ha10 : 0 ≤ a 1 := le_trans hb0 ha1
  have hsq : (beta / 2) ^ 2 ≤ (a 1) ^ 2 := by
    exact (sq_le_sq₀ hb0 ha10).2 ha1
  have hb20 : 0 ≤ beta ^ 2 / 8 := by positivity
  have ha2 : beta ^ 2 / 8 ≤ a 2 := coefficient_one_lower steps
  have ha20 : 0 ≤ a 2 := le_trans hb20 ha2
  have hmul := mul_le_mul ha2 hsq (sq_nonneg (beta / 2)) ha20
  nlinarith

end YangMills.SU2ThetaPrism
