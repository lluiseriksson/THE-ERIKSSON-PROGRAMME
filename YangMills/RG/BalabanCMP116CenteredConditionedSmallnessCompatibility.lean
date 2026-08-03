/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalTermSource
import YangMills.RG.BalabanCMP109PhysicalPivotSmallnessCompatibility

/-!
# A non-vacuous scalar compatibility witness for the centered CMP116 regime

The centered conditioned physical term source asks several smallness
conditions of the same parameters.  This file checks that their scalar target
region is not internally contradictory.  It uses the literal source branching,
contour ratio, geometric row sum, and contour-defect budget.

This is deliberately **not** an inhabitant of
`CMP116Eq226CenteredConditionedPhysicalTermSource`.  In particular, the
numbers called `patchedDefectNorm`, `regionalGreenDefectNorm`,
`precisionNorm`, `rootNorm`, `outerBudget`, and `pivotDefectNorm` below are
target values which the physical producers must still attain.  No
operator-norm estimate or CMP109 diagonal inverse is manufactured from this
arithmetic check.
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
def cmp116CenteredSmallnessWitnessDelta : ℝ := (1 : ℝ) / 20
def cmp116CenteredSmallnessWitnessKappa : ℝ :=
  480 * Real.log 128
def cmp116CenteredSmallnessWitnessSummationRatio : ℝ :=
  (((2 * cmp116SourcePi4TerminalBranching 1 : ℕ) : ℝ))⁻¹

/-- Central registry of the scalar threshold conditions used by the present
centered-conditioned CMP116 source together with the physical CMP109 pivot.

The norm-like entries are explicit *targets* which the physical producers
must attain.  The exponential shell, contour ratio, walk, animal, interaction,
root, outer, and CMP109 pivot conditions retain their literal consumer forms.
Adding another scalar window to this registry makes its witness below fail to
elaborate until the joint regime is updated. -/
structure CMP116CenteredConditionedJointSmallnessRegime
    (d L Nc : ℕ) [NeZero Nc] where
  patchedDefectNorm : ℝ
  regionalGreenDefectNorm : ℝ
  precisionNorm : ℝ
  transposeDefectNorm : ℝ
  rootNorm : ℝ
  outerBudget : ℝ
  qBound : ℝ
  summationRatio : ℝ
  delta : ℝ
  kappa : ℝ
  rho_pos : 0 < cmp116CenteredSmallnessWitnessRho
  radius_pos : 0 < cmp116CenteredSmallnessWitnessRadius
  Ahead_pos : 0 < cmp116CenteredSmallnessWitnessAhead
  patchedDefect_small : patchedDefectNorm < 1
  regional_green_neumann_small : regionalGreenDefectNorm < 1
  shell_small :
    ((2 ^ 4 : ℕ) : ℝ) *
      Real.exp (-cmp116CenteredSmallnessWitnessRate) < 1
  contour_series_small :
    ‖cmp116SourcePi4ComplexContourRatio 1
      cmp116CenteredSmallnessWitnessRho 1‖ < 1
  neumann_small :
    precisionNorm *
      cmp116SourcePi4PhysicalComplexContourDefectBound
        2 1
        cmp116CenteredSmallnessWitnessAhead
        cmp116CenteredSmallnessWitnessRho
        cmp116CenteredSmallnessWitnessRate
        cmp116CenteredSmallnessWitnessRadius 1 < 1
  neumann_transpose_small : transposeDefectNorm < 1
  root_small :
    cmp116CenteredSmallnessWitnessAlpha * rootNorm ^ 2 < 1
  outer_small : 2 * outerBudget ≤ qBound
  interaction_budget :
    cmp116CenteredSmallnessWitnessPotentialRate +
        cmp116CenteredSmallnessWitnessR2Rate +
        cmp116CenteredSmallnessWitnessGamma ≤
      cmp116CenteredSmallnessWitnessAlpha
  qBound_lt_one : qBound < 1
  walk_small :
    ((cmp116SourcePi4TerminalBranching 1 : ℕ) : ℝ) *
      summationRatio < 1
  animal_small :
    64 * Real.exp (-(((1 - 2 * delta) * kappa) / 24)) < 1
  rooted_animal_small :
    64 * Real.exp (-((delta * kappa) / 24)) < 1
  pivot : CMP109PhysicalPivotSmallnessRegime d L Nc

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

/-- The explicit summation-ratio witness leaves a factor-two margin in the
literal grouped-walk contraction. -/
theorem cmp116CenteredSmallnessWitness_walk :
    ((cmp116SourcePi4TerminalBranching 1 : ℕ) : ℝ) *
        cmp116CenteredSmallnessWitnessSummationRatio < 1 := by
  norm_num [cmp116CenteredSmallnessWitnessSummationRatio,
    cmp116SourcePi4TerminalBranching]

/-- The source value `delta = (1/10)(1 - 2/4) = 1/20`, together with the
explicit logarithmic rate, leaves a factor-two margin in the rooted animal
window. -/
theorem cmp116CenteredSmallnessWitness_rootedAnimal :
    64 * Real.exp
      (-((cmp116CenteredSmallnessWitnessDelta *
        cmp116CenteredSmallnessWitnessKappa) / 24)) < 1 := by
  have hcalc :
      (cmp116CenteredSmallnessWitnessDelta *
          cmp116CenteredSmallnessWitnessKappa) / 24 =
        Real.log 128 := by
    rw [cmp116CenteredSmallnessWitnessDelta,
      cmp116CenteredSmallnessWitnessKappa]
    ring
  rw [hcalc, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 128)]
  norm_num

/-- The unrooted residual animal window is stronger at the same source
parameters, because `1 - 2 delta` is larger than `delta`. -/
theorem cmp116CenteredSmallnessWitness_animal :
    64 * Real.exp
      (-(((1 - 2 * cmp116CenteredSmallnessWitnessDelta) *
        cmp116CenteredSmallnessWitnessKappa) / 24)) < 1 := by
  have hroot := cmp116CenteredSmallnessWitness_rootedAnimal
  have hlog : 0 ≤ Real.log 128 := Real.log_nonneg (by norm_num)
  have hresidual :
      ((1 - 2 * cmp116CenteredSmallnessWitnessDelta) *
          cmp116CenteredSmallnessWitnessKappa) / 24 =
        18 * Real.log 128 := by
    rw [cmp116CenteredSmallnessWitnessDelta,
      cmp116CenteredSmallnessWitnessKappa]
    ring
  have hrooted :
      (cmp116CenteredSmallnessWitnessDelta *
          cmp116CenteredSmallnessWitnessKappa) / 24 =
        Real.log 128 := by
    rw [cmp116CenteredSmallnessWitnessDelta,
      cmp116CenteredSmallnessWitnessKappa]
    ring
  have hexp :
      Real.exp (-(18 * Real.log 128)) ≤
        Real.exp (-(Real.log 128)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [hresidual]
  rw [hrooted] at hroot
  nlinarith [mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 64)]

/-- One simultaneous witness for all scalar windows currently registered.
The CMP109 component is the parametric witness already proved for every fixed
dimension, block scale, and nonzero colour count. -/
noncomputable def cmp116CenteredConditionedJointSmallnessRegimeWitness
    (d L Nc : ℕ) [NeZero Nc] :
    CMP116CenteredConditionedJointSmallnessRegime d L Nc where
  patchedDefectNorm := 1 / 4
  regionalGreenDefectNorm := 1 / 4
  precisionNorm := 1
  transposeDefectNorm := 1 / 4
  rootNorm := 1
  outerBudget := 1 / 8
  qBound := 1 / 2
  summationRatio := cmp116CenteredSmallnessWitnessSummationRatio
  delta := cmp116CenteredSmallnessWitnessDelta
  kappa := cmp116CenteredSmallnessWitnessKappa
  rho_pos := by
    norm_num [cmp116CenteredSmallnessWitnessRho,
      cmp116SourcePi4TerminalBranching]
  radius_pos := by norm_num [cmp116CenteredSmallnessWitnessRadius]
  Ahead_pos := by norm_num [cmp116CenteredSmallnessWitnessAhead]
  patchedDefect_small := by norm_num
  regional_green_neumann_small := by norm_num
  shell_small := cmp116CenteredSmallnessWitness_shell
  contour_series_small := cmp116CenteredSmallnessWitness_contourRatio
  neumann_small := by
    simpa using cmp116CenteredSmallnessWitness_contourDefect
  neumann_transpose_small := by norm_num
  root_small := by norm_num [cmp116CenteredSmallnessWitnessAlpha]
  outer_small := by norm_num
  interaction_budget := by
    norm_num [cmp116CenteredSmallnessWitnessPotentialRate,
      cmp116CenteredSmallnessWitnessR2Rate,
      cmp116CenteredSmallnessWitnessGamma,
      cmp116CenteredSmallnessWitnessAlpha]
  qBound_lt_one := by norm_num
  walk_small := cmp116CenteredSmallnessWitness_walk
  animal_small := cmp116CenteredSmallnessWitness_animal
  rooted_animal_small := cmp116CenteredSmallnessWitness_rootedAnimal
  pivot := cmp109PhysicalPivotSmallnessRegimeWitness d L Nc

/-- All scalar inequalities requested by the present centered-conditioned
consumer, together with the future CMP109 pivot defect, have a simultaneous
strictly positive target witness.

The first two strict norm targets record, separately, the patched one-cochain
defect and the regional zero-cochain Green defect at `1/4`.  The later
Neumann inequalities use target precision row/column norm one, the root
window uses target root norm one, and the pivot entry is the future diagonal
defect.  These are named targets, not proofs about the corresponding physical
operators. -/
theorem cmp116CenteredConditioned_scalarSmallness_nonempty :
    let patchedDefectNorm : ℝ := 1 / 4
    let regionalGreenDefectNorm : ℝ := 1 / 4
    let precisionNorm : ℝ := 1
    let rootNorm : ℝ := 1
    let outerBudget : ℝ := 1 / 8
    let qBound : ℝ := 1 / 2
    let pivotDefectNorm : ℝ := 1 / 4
    0 < cmp116CenteredSmallnessWitnessRho ∧
    0 < cmp116CenteredSmallnessWitnessRadius ∧
    0 < cmp116CenteredSmallnessWitnessAhead ∧
    patchedDefectNorm < 1 ∧
    regionalGreenDefectNorm < 1 ∧
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
