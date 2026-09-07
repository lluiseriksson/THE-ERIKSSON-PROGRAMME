/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99UbarSpecialUnitary
import YangMills.RG.NearLogDeviationBudget

/-!
# CMP99 Ubar from one uniform physical deviation budget

The special-unitary Ubar constructor previously exposed two pointwise
premises: membership in the Mercator ball and a bound on `nearLog`.  This file
derives both from one source-facing estimate `‖D i - 1‖ ≤ δ` and the explicit
scalar no-winding budget.

The producer of that physical deviation estimate remains deliberately open.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- Every logarithm in the physical weighted exponent is traceless from one
uniform deviation budget. -/
theorem trace_cmp99UbarSpecialUnitaryExponent_eq_zero_of_deviationBudget
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ) :
    Matrix.trace (cmp99UbarSpecialUnitaryExponent s w D) = 0 := by
  exact trace_cmp99UbarSpecialUnitaryExponent_eq_zero s w D
    (fun i hi => B.nearIdentity
      (D i : Matrix (Fin Nc) (Fin Nc) ℂ) (hdev i hi))
    (fun i hi => B.nearLog_noWinding
      (D i : Matrix (Fin Nc) (Fin Nc) ℂ) (hdev i hi))

/-- **Canonical CMP99 special-unitary factor from one physical budget.** -/
noncomputable def cmp99UbarSpecialUnitaryFactorOfDeviationBudget
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ) : SUN Nc :=
  cmp99UbarSpecialUnitaryFactorOfNearIdentity s w D
    (fun i hi => B.nearIdentity
      (D i : Matrix (Fin Nc) (Fin Nc) ℂ) (hdev i hi))
    (fun i hi => B.nearLog_noWinding
      (D i : Matrix (Fin Nc) (Fin Nc) ℂ) (hdev i hi))

@[simp] theorem cmp99UbarSpecialUnitaryFactorOfDeviationBudget_coe
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ) :
    (cmp99UbarSpecialUnitaryFactorOfDeviationBudget
      s w D B hdev : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialUnitaryExponent s w D) :=
  rfl

/-- The complete Ubar block remains in `SU(Nc)` and now consumes only one
uniform deviation estimate for the local factors. -/
noncomputable def cmp99UbarSpecialUnitaryBlockOfDeviationBudget
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (coarse : SUN Nc) : SUN Nc :=
  cmp99UbarSpecialUnitaryFactorOfDeviationBudget s w D B hdev * coarse

@[simp] theorem cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (coarse : SUN Nc) :
    (cmp99UbarSpecialUnitaryBlockOfDeviationBudget
      s w D B hdev coarse : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialUnitaryExponent s w D) *
        (coarse : Matrix (Fin Nc) (Fin Nc) ℂ) :=
  rfl

end

end YangMills.RG
