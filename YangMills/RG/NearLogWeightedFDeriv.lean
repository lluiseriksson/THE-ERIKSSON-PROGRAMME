/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogTermFDeriv

/-!
# Linearization of the finite logarithmic average

The nonlinear block variable in CMP98/CMP99 is the exponential of a finite
weighted sum of local logarithms.  This file proves the exact first-derivative
rule at a matching background, where every represented deviation is zero.

The result is source-shaped: the derivative is the same weighted sum of the
derivatives of the individual physical deviations.  In particular, it does
not replace those derivatives by an arbitrary completed `Q(U)` operator.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {𝔸 E ι : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite weighted sum of local logarithms has derivative equal to the
same weighted sum of the derivatives of its zero-based deviation maps. -/
theorem hasFDerivAt_weightedNearLogSum_of_eq_zero
    (S : Finset ι) (w : ι → ℝ)
    (F : ι → E → 𝔸) (F' : ι → E →L[ℝ] 𝔸) (x : E)
    (hF : ∀ i ∈ S, HasFDerivAt (F i) (F' i) x)
    (hzero : ∀ i ∈ S, F i x = 0) :
    HasFDerivAt
      (fun y => ∑ i ∈ S, w i • nearLog (F i y))
      (∑ i ∈ S, w i • F' i) x := by
  exact HasFDerivAt.fun_sum fun i hi =>
    (HasFDerivAt.nearLog_of_eq_zero (hF i hi) (hzero i hi)).const_smul (w i)

/-- Exponentiating the finite logarithmic average does not change its first
derivative at a matching background, because the exponent itself vanishes
there and the Banach-algebra exponential has identity derivative at zero. -/
theorem hasFDerivAt_exp_weightedNearLogSum_of_eq_zero
    (S : Finset ι) (w : ι → ℝ)
    (F : ι → E → 𝔸) (F' : ι → E →L[ℝ] 𝔸) (x : E)
    (hF : ∀ i ∈ S, HasFDerivAt (F i) (F' i) x)
    (hzero : ∀ i ∈ S, F i x = 0) :
    HasFDerivAt
      (fun y => NormedSpace.exp (∑ i ∈ S, w i • nearLog (F i y)))
      (∑ i ∈ S, w i • F' i) x := by
  have havg := hasFDerivAt_weightedNearLogSum_of_eq_zero
    S w F F' x hF hzero
  have hvalue : (∑ i ∈ S, w i • nearLog (F i x)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i hi, nearLog_zero, smul_zero]
  have hexp : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      (ContinuousLinearMap.id ℝ 𝔸)
      (∑ i ∈ S, w i • nearLog (F i x)) := by
    simpa [hvalue] using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸))
  simpa using hexp.comp x havg

/-- Linearization of the literal finite logarithmic average at a nontrivial
near-identity background.  Every local derivative is the complete ordered
Mercator derivative composed with the derivative of its physical deviation;
no `Q(U)` operator is supplied as an independent argument. -/
theorem hasFDerivAt_weightedNearLogSum_of_norm_lt_one [NormOneClass 𝔸]
    (S : Finset ι) (w : ι → ℝ)
    (F : ι → E → 𝔸) (F' : ι → E →L[ℝ] 𝔸) (x : E)
    (hF : ∀ i ∈ S, HasFDerivAt (F i) (F' i) x)
    (hnorm : ∀ i ∈ S, ‖F i x‖ < 1) :
    HasFDerivAt
      (fun y => ∑ i ∈ S, w i • nearLog (F i y))
      (∑ i ∈ S, w i •
        ((∑' n : ℕ, nearLogTermFDeriv (F i x) n).comp (F' i))) x := by
  exact HasFDerivAt.fun_sum fun i hi =>
    (HasFDerivAt.nearLog_of_norm_lt_one (hF i hi) (hnorm i hi)).const_smul (w i)

end

end YangMills.RG
