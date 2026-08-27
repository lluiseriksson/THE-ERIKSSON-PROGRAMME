import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
Minimal elaboration gate for the operator-extensionality tail used by
`BalabanCMP99Eq335PhysicalLaplacianInternalCarrier`.

This file is runner instrumentation only: it mentions no project declaration
and must pass before the long physical focal is attempted.
-/

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example (KU KV : E →L[ℝ] E)
    (hKU : KU.IsSymmetric) (hKV : KV.IsSymmetric)
    (hquad : ∀ phi, inner ℝ phi (KU phi) = inner ℝ phi (KV phi)) :
    KU = KV := by
  have hzero : (KU - KV).toLinearMap = 0 := by
    apply ((hKU.sub hKV).inner_map_self_eq_zero).mp
    intro phi
    change inner ℝ (KU phi - KV phi) phi = 0
    rw [inner_sub_left]
    rw [hKU phi phi, hKV phi phi, hquad phi]
    exact sub_self _
  rw [← sub_eq_zero]
  apply ContinuousLinearMap.ext
  intro phi
  simpa using congrArg (fun T => T phi) hzero

