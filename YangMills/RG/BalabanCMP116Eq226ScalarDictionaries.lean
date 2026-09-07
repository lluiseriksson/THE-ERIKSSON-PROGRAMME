/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger

/-!
# Scalar source dictionaries for the CMP116 equation-(2.26) ledger

The terminal contour estimate compares three scalar penalties whose indices
come from different physical presentations: the selected `P` bonds, the
normalized gap, and the Gaussian volume.  This module derives the required
penalty comparisons from exact parameter/cardinality dictionaries and one
genuine scalar volume budget.  It does not assume any of the three complete
penalty inequalities.
-/

namespace YangMills.RG

noncomputable section

/-- Exact equality of the `P` cardinality penalties after identifying the
physical parameters and the cardinalities of the two bond encodings. -/
theorem cmp116Eq226PBondPenalty_eq_of_sourceDictionary
    {ιP ιP' : Type*}
    (sourceGamma sourceEpsilon sourceGk : ℝ)
    (sourceP : Finset ιP)
    (targetGamma targetEpsilon targetGk : ℝ)
    (targetP : Finset ιP')
    (hgamma : targetGamma = sourceGamma)
    (hepsilon : targetEpsilon = sourceEpsilon)
    (hgk : targetGk = sourceGk)
    (hcard : targetP.card = sourceP.card) :
    targetGamma * targetEpsilon ^ 2 * (targetGk ^ 2)⁻¹ *
          (targetP.card : ℝ) =
      sourceGamma * sourceEpsilon ^ 2 * (sourceGk ^ 2)⁻¹ *
          (sourceP.card : ℝ) := by
  rw [hgamma, hepsilon, hgk, hcard]

/-- Exact equality of the normalized gap penalties after identifying the
source parameter, physical scale product, and gap cardinality. -/
theorem cmp116Eq226GapPenalty_eq_of_sourceDictionary
    (sourceKappa1 : ℝ) (sourceL sourceM sourceGapCard : ℕ)
    (targetKappa1 : ℝ) (targetL targetM targetGapCard : ℕ)
    (hkappa1 : targetKappa1 = sourceKappa1)
    (hscale : targetL * targetM = sourceL * sourceM)
    (hcard : targetGapCard = sourceGapCard) :
    (targetKappa1 - 1) *
          ((((targetL * targetM : ℕ) : ℝ) ^ 4)⁻¹) *
          (targetGapCard : ℝ) =
      (sourceKappa1 - 1) *
          ((((sourceL * sourceM : ℕ) : ℝ) ^ 4)⁻¹) *
          (sourceGapCard : ℝ) := by
  rw [hkappa1, hscale, hcard]

/-- The Gaussian-volume exponent comparison follows from a coefficient
budget, monotonicity of the physical source cardinality, and nonnegativity of
the target coefficient. -/
theorem cmp116Eq226GaussianExponent_le_of_sourceDictionary
    (sourceCoefficient targetCoefficient : ℝ)
    (sourceCard targetCard : ℕ)
    (hcoefficient : sourceCoefficient ≤ targetCoefficient)
    (hcard : sourceCard ≤ targetCard)
    (htarget_nonneg : 0 ≤ targetCoefficient) :
    sourceCoefficient * (sourceCard : ℝ) ≤
      targetCoefficient * (targetCard : ℝ) := by
  calc
    sourceCoefficient * (sourceCard : ℝ) ≤
        targetCoefficient * (sourceCard : ℝ) := by
      exact
        mul_le_mul_of_nonneg_right hcoefficient
          (Nat.cast_nonneg sourceCard)
    _ ≤ targetCoefficient * (targetCard : ℝ) := by
      exact
        mul_le_mul_of_nonneg_left
          (by exact_mod_cast hcard)
          htarget_nonneg

end

end YangMills.RG
