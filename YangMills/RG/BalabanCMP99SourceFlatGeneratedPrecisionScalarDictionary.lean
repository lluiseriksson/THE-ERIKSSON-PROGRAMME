/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Scalar dictionary for the generated flat precision

After `depth` order-`M` block maps, the literal one-block side is
`R = M^depth`.  The flat full-complex precision uses `R^2` in front of its
unit-spacing stencil and a coefficient-one weighted adjoint, whereas the
generated real precision uses physical spacing and the counting-space
adjoint.  This file records only the scalar conversion:

* physical spacing is `R⁻¹`, so its inverse square is `R^2`;
* the full-complex averaging parameter is generated mass times `R⁻ᵈ`;
* multiplying that parameter by the weighted-adjoint kernel coefficient
  `R⁻ᵈ` gives the generated counting coefficient
  `generatedMass * (R⁻ᵈ)^2`.

No carrier, Laplacian, complexification, precision or inverse equality is
asserted here.
-/

namespace YangMills.RG

noncomputable section

/-- Literal one-block side of a depth-`depth` generated flat tower. -/
def cmp99SourceGeneratedFullComplexBlockSide (M depth : ℕ) : ℕ :=
  M ^ depth

/-- Physical spacing whose inverse is the literal terminal block side. -/
noncomputable def cmp99SourceGeneratedFullComplexSpacing
    (M depth : ℕ) : ℝ :=
  ((cmp99SourceGeneratedFullComplexBlockSide M depth : ℕ) : ℝ)⁻¹

/-- Full-complex coefficient paired with the coefficient-one source weighted
adjoint.  The extra one-block weight converts it to the generated
counting-space mass coefficient. -/
noncomputable def cmp99SourceGeneratedFullComplexA
    (d M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99SourceGeneratedPhysicalMass d M depth spacing epsilon *
    cmp99SourceBlockAverageWeight
      (cmp99SourceGeneratedFullComplexBlockSide M depth) d

@[simp] theorem cmp99SourceGeneratedFullComplexBlockSide_eq
    (M depth : ℕ) :
    cmp99SourceGeneratedFullComplexBlockSide M depth = M ^ depth := rfl

/-- Exact scalar match between generated physical spacing and the stencil
coefficient used by the one-block full-complex precision. -/
theorem cmp99SourceGeneratedFullComplexSpacing_inv_mul_inv
    (M depth : ℕ) :
    (cmp99SourceGeneratedFullComplexSpacing M depth)⁻¹ *
        (cmp99SourceGeneratedFullComplexSpacing M depth)⁻¹ =
      (((cmp99SourceGeneratedFullComplexBlockSide M depth : ℕ) : ℝ)) ^ 2 := by
  unfold cmp99SourceGeneratedFullComplexSpacing
  simp only [inv_inv, pow_two]

/-- The full-complex averaging coefficient times its one-block weighted
adjoint coefficient is exactly the generated counting-space coefficient. -/
theorem cmp99SourceGeneratedFullComplexA_mul_weight
    (d M depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourceGeneratedFullComplexA d M depth spacing epsilon *
        cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide M depth) d =
      cmp99SourceGeneratedPhysicalMass d M depth spacing epsilon *
        (cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide M depth) d) ^ 2 := by
  unfold cmp99SourceGeneratedFullComplexA
  ring

/-- Complex-cast form consumed by the literal full-complex precision. -/
theorem cmp99SourceGeneratedFullComplexA_mul_weight_complex
    (d M depth : ℕ) (spacing epsilon : ℝ) :
    ((cmp99SourceGeneratedFullComplexA d M depth spacing epsilon : ℝ) : ℂ) *
        ((cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide M depth) d : ℝ) : ℂ) =
      ((cmp99SourceGeneratedPhysicalMass d M depth spacing epsilon : ℝ) : ℂ) *
        ((cmp99SourceBlockAverageWeight
          (cmp99SourceGeneratedFullComplexBlockSide M depth) d : ℝ) : ℂ) ^ 2 := by
  exact_mod_cast cmp99SourceGeneratedFullComplexA_mul_weight
    d M depth spacing epsilon

end

end YangMills.RG
