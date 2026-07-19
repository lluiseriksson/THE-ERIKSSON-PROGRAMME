/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.MatrixDetExpSkewAdjoint
import YangMills.RG.BalabanCMP99UbarUnitaryCFC

/-!
# The canonical CMP99 Ubar block in the special unitary group

This file consumes the determinant/exponential and no-winding closures.  A
finite weighted sum of principal logarithms of near-identity special unitary
matrices is skew-adjoint and traceless; its exponential therefore lies in
`SU(Nc)`.  No trace-quantization certificate is exposed to the caller.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance matrixL2CStarAlgebraForUbar :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

local instance matrixRealComplexScalarTowerForUbar :
    IsScalarTower ℝ ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) where
  smul_assoc r c X := by
    ext i j
    exact smul_assoc r c (X i j)

local instance matrixRationalNormedAlgebraForUbar :
    NormedAlgebra ℚ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-- The literal CMP99 exponent for special-unitary deviations. -/
noncomputable def cmp99UbarSpecialUnitaryExponent {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp99UbarUnitaryExponent s w (fun i => specialUnitaryToUnitary (D i))

/-- Every principal logarithm in the weighted exponent is traceless once its
individual no-winding budget is supplied; hence so is their finite sum. -/
theorem trace_cmp99UbarSpecialUnitaryExponent_eq_zero {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    Matrix.trace (cmp99UbarSpecialUnitaryExponent s w D) = 0 := by
  unfold cmp99UbarSpecialUnitaryExponent cmp99UbarUnitaryExponent
    cmp99UbarExponent
  change Matrix.trace
      (∑ i ∈ s, w i •
        nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have htrace : Matrix.trace
      (nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0 :=
    trace_nearLog_unitary_sub_one_eq_zero_of_det_eq_one_of_noWinding
      (specialUnitaryToUnitary (D i)) (hD i hi)
      (Matrix.mem_specialUnitaryGroup_iff.mp (D i).property).2
      (hnoWinding i hi)
  unfold Matrix.trace at htrace ⊢
  have htrace' : ∑ j,
      nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) j j = 0 := by
    simpa only [Matrix.diag] using htrace
  change ∑ j, (w i : ℂ) *
      nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) j j = 0
  rw [← Finset.mul_sum, htrace', mul_zero]

/-- The physical hypotheses make the complete special-unitary exponent
skew-adjoint. -/
theorem cmp99UbarSpecialUnitaryExponent_mem_skewAdjoint {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1) :
    cmp99UbarSpecialUnitaryExponent s w D ∈
      skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) := by
  exact @cmp99UbarUnitaryExponent_mem_skewAdjoint
    (Matrix (Fin Nc) (Fin Nc) ℂ) matrixL2CStarAlgebraForUbar
    inferInstance matrixRealComplexScalarTowerForUbar
    matrixRationalNormedAlgebraForUbar ι s w
    (fun i => specialUnitaryToUnitary (D i)) hD

/-- **Canonical special-unitary CMP99 factor.** -/
noncomputable def cmp99UbarSpecialUnitaryFactorOfNearIdentity {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) : SUN Nc :=
  ⟨NormedSpace.exp (cmp99UbarSpecialUnitaryExponent s w D),
    Matrix.exp_mem_specialUnitaryGroup_of_mem_skewAdjoint_of_trace_eq_zero
      (cmp99UbarSpecialUnitaryExponent s w D)
      (cmp99UbarSpecialUnitaryExponent_mem_skewAdjoint s w D hD)
      (trace_cmp99UbarSpecialUnitaryExponent_eq_zero s w D hD hnoWinding)⟩

@[simp] theorem cmp99UbarSpecialUnitaryFactorOfNearIdentity_coe
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    (cmp99UbarSpecialUnitaryFactorOfNearIdentity
      s w D hD hnoWinding : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialUnitaryExponent s w D) :=
  rfl

/-- The complete Ubar block remains in `SU(Nc)` after multiplication by the
coarse special-unitary background. -/
noncomputable def cmp99UbarSpecialUnitaryBlockOfNearIdentity {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi)
    (coarse : SUN Nc) : SUN Nc :=
  cmp99UbarSpecialUnitaryFactorOfNearIdentity s w D hD hnoWinding * coarse

@[simp] theorem cmp99UbarSpecialUnitaryBlockOfNearIdentity_coe
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi)
    (coarse : SUN Nc) :
    (cmp99UbarSpecialUnitaryBlockOfNearIdentity
      s w D hD hnoWinding coarse : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialUnitaryExponent s w D) *
        (coarse : Matrix (Fin Nc) (Fin Nc) ℂ) :=
  rfl

end

end YangMills.RG
