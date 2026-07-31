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

/-- A real character family indexed by twice-spin.  This is data, not a claim
that every supplied function is already a constructed irreducible character. -/
abbrev RealCharacterFamily := TwiceSpin → SU2 → ℝ

/-- Registered coefficient integral. -/
def alpha (characters : RealCharacterFamily) (beta : ℝ) (j : TwiceSpin) : ℝ :=
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
