/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalTermSource

/-!
# A non-vacuous scalar compatibility witness for the centered CMP116 regime

The centered conditioned physical term source asks several smallness
conditions of the same parameters.  This file checks that their scalar target
region is not internally contradictory.  It uses the literal source branching,
contour ratio, geometric row sum, and contour-defect budget.

This is deliberately **not** an inhabitant of
`CMP116Eq226CenteredConditionedPhysicalTermSource`.  In particular, the
numbers called `patchedDefectNorm`, `precisionNorm`, `rootNorm`,
`outerBudget`, and `pivotDefectNorm` below are target values which the
physical producers must still attain.  No operator-norm estimate or CMP109
diagonal inverse is manufactured from this arithmetic check.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit target parameters for the simultaneous scalar smallness check.
The contour parameters are all strictly positive; none of the contour
conditions is discharged by setting its amplitude or radius to zero. -/
def cmp116CenteredSmallnessWitnessRate : ℝ := Real.log 32
def cmp116CenteredSmallnessWitnessRho : ℝ :=
  ((4 * cmp116SourcePi4TerminalBranching 1 : ℕ) : ℝ)⁻¹
def cmp116CenteredSmallnessWitnessRadius : ℝ := (1 : ℝ) / 1000000
def cmp116CenteredSmallnessWitnessAhead : ℝ := (1 : ℝ) / 1000000
def cmp116CenteredSmallnessWitnessAlpha : ℝ := (1 : ℝ) / 16
def cmp116CenteredSmallnessWitnessPotentialRate : ℝ := (1 : ℝ) / 64
def cmp116CenteredSmallnessWitnessR2Rate : ℝ := (1 : ℝ) / 64
def cmp116CenteredSmallnessWitnessGamma : ℝ := (1 : ℝ) / 64

/-- At the explicit rate `log 32`, the four-dimensional shell factor is
exactly one half. -/
theorem cmp116CenteredSmallnessWitness_shell :
    ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-cmp116CenteredSmallnessWitnessRate) < 1 := by
  rw [cmp116CenteredSmallnessWitnessRate, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 32)]
  norm_num

/-- The literal CMP116 terminal branching and the positive witness `rho`
give contour ratio exactly one quarter at `Rweak = 1`. -/
theorem cmp116CenteredSmallnessWitness_contourRatio :
    ‖cmp116SourcePi4ComplexContourRatio 1
        cmp116CenteredSmallnessWitnessRho 1‖ < 1 := by
  norm_num [cmp116CenteredSmallnessWitnessRho,
    cmp116SourcePi4ComplexContourRatio,
    cmp116SourcePi4TerminalBranching]

/-- The explicit physical contour-defect budget is already below one at the
nonzero witness amplitudes, for the smallest nonabelian colour count `Nc=2`.
This is the shared scalar input of both Neumann inequalities when the target
precision row and column norms are at most one. -/
theorem cmp116CenteredSmallnessWitness_contourDefect :
    cmp116SourcePi4PhysicalComplexContourDefectBound
        2 1
        cmp116CenteredSmallnessWitnessAhead
        cmp116CenteredSmallnessWitnessRho
        cmp116CenteredSmallnessWitnessRate
        cmp116CenteredSmallnessWitnessRadius 1 < 1 := by
  rw [cmp116CenteredSmallnessWitnessRate]
  simp only [cmp116SourcePi4PhysicalComplexContourDefectBound,
    cmp116SourcePi4ComplexContourPrefactor,
    cmp116SourcePi4ComplexContourRatio,
    cmp116CenteredSmallnessWitnessAhead,
    cmp116CenteredSmallnessWitnessRadius,
    cmp116CenteredSmallnessWitnessRho,
    cmp116SourcePi4TerminalBranching,
    cmp99PhysicalBondGeometricRowSum,
    Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 32)]
  norm_num

/-- All scalar inequalities requested by the present centered-conditioned
consumer, together with the future CMP109 pivot defect, have a simultaneous
strictly positive target witness.

The first conjunct records the target patched-parametrix norm `1/4`; the
fourth and fifth use target precision row/column norm one; the sixth uses
target root norm one; and the eighth is the future diagonal pivot defect.
These are named targets, not proofs about the corresponding physical
operators. -/
theorem cmp116CenteredConditioned_scalarSmallness_nonempty :
    let patchedDefectNorm : ℝ := 1 / 4
    let precisionNorm : ℝ := 1
    let rootNorm : ℝ := 1
    let outerBudget : ℝ := 1 / 8
    let qBound : ℝ := 1 / 2
    let pivotDefectNorm : ℝ := 1 / 4
    0 < cmp116CenteredSmallnessWitnessRho ∧
    0 < cmp116CenteredSmallnessWitnessRadius ∧
    0 < cmp116CenteredSmallnessWitnessAhead ∧
    patchedDefectNorm < 1 ∧
    ((2 ^ 4 : ℕ) : ℝ) *
        Real.exp (-cmp116CenteredSmallnessWitnessRate) < 1 ∧
    ‖cmp116SourcePi4ComplexContourRatio 1
        cmp116CenteredSmallnessWitnessRho 1‖ < 1 ∧
    precisionNorm *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          2 1
          cmp116CenteredSmallnessWitnessAhead
          cmp116CenteredSmallnessWitnessRho
          cmp116CenteredSmallnessWitnessRate
          cmp116CenteredSmallnessWitnessRadius 1 < 1 ∧
    precisionNorm *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          2 1
          cmp116CenteredSmallnessWitnessAhead
          cmp116CenteredSmallnessWitnessRho
          cmp116CenteredSmallnessWitnessRate
          cmp116CenteredSmallnessWitnessRadius 1 < 1 ∧
    cmp116CenteredSmallnessWitnessAlpha * rootNorm ^ 2 < 1 ∧
    2 * outerBudget ≤ qBound ∧
    pivotDefectNorm < 1 ∧
    cmp116CenteredSmallnessWitnessPotentialRate +
        cmp116CenteredSmallnessWitnessR2Rate +
        cmp116CenteredSmallnessWitnessGamma ≤
      cmp116CenteredSmallnessWitnessAlpha ∧
    qBound < 1 := by
  dsimp only
  constructor
  · norm_num [cmp116CenteredSmallnessWitnessRho,
      cmp116SourcePi4TerminalBranching]
  constructor
  · norm_num [cmp116CenteredSmallnessWitnessRadius]
  constructor
  · norm_num [cmp116CenteredSmallnessWitnessAhead]
  constructor
  · norm_num
  constructor
  · exact cmp116CenteredSmallnessWitness_shell
  constructor
  · exact cmp116CenteredSmallnessWitness_contourRatio
  constructor
  · simpa using cmp116CenteredSmallnessWitness_contourDefect
  constructor
  · simpa using cmp116CenteredSmallnessWitness_contourDefect
  constructor
  · norm_num [cmp116CenteredSmallnessWitnessAlpha]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num [cmp116CenteredSmallnessWitnessPotentialRate,
      cmp116CenteredSmallnessWitnessR2Rate,
      cmp116CenteredSmallnessWitnessGamma,
      cmp116CenteredSmallnessWitnessAlpha]
  · norm_num

end

end YangMills.RG
