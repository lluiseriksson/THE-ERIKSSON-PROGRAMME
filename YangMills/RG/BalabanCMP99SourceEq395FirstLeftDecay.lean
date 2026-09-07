/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395AmbientMiddleDecay

/-!
# Exponential decay of the first left factor in CMP99 equation (3.95)

The exterior source characteristic is a contractive diagonal multiplier.
Consequently it preserves the volume-independent exponential kernel bound of
the literal ambient global middle.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

namespace CMP99SourceDependentOmegaGeometry

/-- The complement of the literal source characteristic is itself the
expected diagonal scalar multiplier. -/
theorem one_sub_cmp99Eq395PhysicalSourceCharacteristic_eq
    (cell : FinBox 4 Q) :
    (1 - cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell) =
      finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
        (fun block : FinBox 4 (2 * Q) =>
          1 - cmp99SourcePiCharacteristic cell block) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro block
  simp [cmp99Eq395PhysicalSourceCharacteristic,
    finitePiLpScalarMultiplier_apply, sub_smul]

/-- The scalar exterior characteristic is pointwise contractive. -/
theorem norm_one_sub_cmp99SourcePiCharacteristic_le_one
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    ‖1 - cmp99SourcePiCharacteristic cell block‖ ≤ 1 := by
  classical
  unfold cmp99SourcePiCharacteristic
  split <;> norm_num

set_option maxRecDepth 4000 in
set_option maxHeartbeats 12000000 in
/-- The exterior-cut global middle preserves the full exponential rate and
amplitude of the ambient generated middle. -/
theorem cmp99Eq395PhysicalFirstLeft_exponentialKernelBound
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99Eq395PhysicalFirstLeft hM depth hspacing background budget
        fineSmall hsmall cell)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 4) := by
  let Middle := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background
    budget fineSmall hsmall
  have hMiddle : FinitePiLpTypedExponentialKernelBound Middle
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 4) :=
    cmp99Eq395PhysicalGlobalMiddle_exponentialKernelBound
      hM depth hspacing background budget fineSmall hsmall
  have hcut :=
    finitePiLpTypedExponentialKernelBound_comp_scalarMultiplier_left
      (fun block : FinBox 4 (2 * Q) =>
        1 - cmp99SourcePiCharacteristic cell block)
      Middle (norm_one_sub_cmp99SourcePiCharacteristic_le_one cell) hMiddle
  rw [cmp99Eq395PhysicalFirstLeft,
    one_sub_cmp99Eq395PhysicalSourceCharacteristic_eq]
  exact hcut

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG

