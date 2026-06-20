/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Gaussian block kernels as normalized finite RG steps

This file isolates the measure-theoretic core of a finite Gaussian block
fluctuation step.  Given a coarse field `A`, a continuous linear averaging map
`Q`, and a fluctuation law `gamma`, the conditional output law is the translate
of `gamma` by `Q A`.  Equivalently, a full one-step free block transform is the
pushforward of the product law `(coarse field, fluctuation)` by
`(A, noise) |-> Q A + noise`.

The point is deliberately modest but useful for the Appendix-F / Balaban track:
normalization of the finite Gaussian collar is now a theorem, not an implicit
analytic side condition.  No covariance decay, Hessian normalization, or
source-specific constant is claimed here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Kernel

variable [MeasurableSpace F]

/-- The conditional Gaussian block kernel at coarse field `A`: sample a
fluctuation from `gamma` and output `Q A + noise`. -/
noncomputable def gaussianBlockKernel (Q : E →L[ℝ] F) (gamma : Measure F) (A : E) :
    Measure F :=
  gamma.map fun noise => Q A + noise

variable [BorelSpace F]

/-- Translating a probability fluctuation law gives a probability conditional
block kernel. -/
theorem gaussianBlockKernel_isProbability (Q : E →L[ℝ] F) (gamma : Measure F)
    [IsProbabilityMeasure gamma] (A : E) :
    IsProbabilityMeasure (gaussianBlockKernel Q gamma A) := by
  unfold gaussianBlockKernel
  apply Measure.isProbabilityMeasure_map
  fun_prop

@[simp]
theorem gaussianBlockKernel_univ (Q : E →L[ℝ] F) (gamma : Measure F)
    [IsProbabilityMeasure gamma] (A : E) :
    gaussianBlockKernel Q gamma A Set.univ = 1 := by
  have hprob := gaussianBlockKernel_isProbability Q gamma A
  rw [measure_univ]

end Kernel

section Transform

variable [MeasurableSpace E] [MeasurableSpace F]

/-- The full free Gaussian block transform: sample a coarse field from `mu`, a
fluctuation from `gamma`, and output `Q A + noise`.  This is the finite normalized collar before any interacting
Appendix-F activity is inserted. -/
noncomputable def gaussianBlockTransform (Q : E →L[ℝ] F) (mu : Measure E) (gamma : Measure F) :
    Measure F :=
  (mu.prod gamma).map fun p : E × F => Q p.1 + p.2

variable [BorelSpace E] [BorelSpace F] [SecondCountableTopology F]

/-- A product of probability laws pushed through the finite block map is still a
probability law.  This is the normalization theorem for the free finite block
step. -/
theorem gaussianBlockTransform_isProbability (Q : E →L[ℝ] F) (mu : Measure E) (gamma : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure gamma] :
    IsProbabilityMeasure (gaussianBlockTransform Q mu gamma) := by
  unfold gaussianBlockTransform
  apply Measure.isProbabilityMeasure_map
  fun_prop

@[simp]
theorem gaussianBlockTransform_univ (Q : E →L[ℝ] F) (mu : Measure E) (gamma : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure gamma] :
    gaussianBlockTransform Q mu gamma Set.univ = 1 := by
  have hprob := gaussianBlockTransform_isProbability Q mu gamma
  rw [measure_univ]

end Transform

end YangMills.RG
