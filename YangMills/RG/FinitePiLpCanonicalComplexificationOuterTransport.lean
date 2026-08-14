/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpCanonicalComplexification

/-!
# Outer-norm transport for canonical finite complexification

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

The real generated operators are stored on a finite counting-Hilbert
`PiLp 2` space, while the literal full-box complex precision is packaged on
the ordinary finite function space.  These spaces have the same coordinates
but not the same normed-space type.  This file conjugates the canonical
complexification by Mathlib's explicit continuous `PiLp` equivalence and
proves that composition and identity remain exact after that norm transport.

No physical precision, inverse, Green operator, or carrier dictionary is
accepted or identified here.
-/

namespace YangMills.RG

noncomputable section

universe u v

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

/-- Canonical continuous coordinate equivalence from the outer counting
`PiLp 2` space to the ordinary finite function space. -/
noncomputable def finitePiLpComplexOuterEquiv :
    FinitePiLpField ι (EuclideanSpace ℂ κ) ≃L[ℂ]
      (ι → EuclideanSpace ℂ κ) :=
  PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : ι => EuclideanSpace ℂ κ)

@[simp] theorem finitePiLpComplexOuterEquiv_apply
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) (i : ι) (a : κ) :
    finitePiLpComplexOuterEquiv z i a = z i a := rfl

/-- Canonical complexification presented on the ordinary finite function
space by conjugating through the explicit outer `PiLp` equivalence. -/
noncomputable def finitePiLpCanonicalComplexificationOuterCLM
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    (ι → EuclideanSpace ℂ κ) →L[ℂ]
      (ι → EuclideanSpace ℂ κ) :=
  finitePiLpComplexOuterEquiv.toContinuousLinearMap.comp
    ((finitePiLpCanonicalComplexificationCLM T).comp
      finitePiLpComplexOuterEquiv.symm.toContinuousLinearMap)

/-- The outer-norm presentation preserves composition exactly. -/
theorem finitePiLpCanonicalComplexificationOuterCLM_comp
    (S T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpCanonicalComplexificationOuterCLM (S.comp T) =
      (finitePiLpCanonicalComplexificationOuterCLM S).comp
        (finitePiLpCanonicalComplexificationOuterCLM T) := by
  apply ContinuousLinearMap.ext
  intro z
  have h := congrArg
    (fun A : FinitePiLpField ι (EuclideanSpace ℂ κ) →L[ℂ]
        FinitePiLpField ι (EuclideanSpace ℂ κ) =>
      finitePiLpComplexOuterEquiv
        (A (finitePiLpComplexOuterEquiv.symm z)))
    (finitePiLpCanonicalComplexificationCLM_comp S T)
  simpa [finitePiLpCanonicalComplexificationOuterCLM] using h

/-- The outer-norm presentation sends the real identity to the complex
identity. -/
theorem finitePiLpCanonicalComplexificationOuterCLM_id :
    finitePiLpCanonicalComplexificationOuterCLM
        (ContinuousLinearMap.id ℝ
          (FinitePiLpField ι (EuclideanSpace ℝ κ))) =
      ContinuousLinearMap.id ℂ (ι → EuclideanSpace ℂ κ) := by
  apply ContinuousLinearMap.ext
  intro z
  have h := congrArg
    (fun A : FinitePiLpField ι (EuclideanSpace ℂ κ) →L[ℂ]
        FinitePiLpField ι (EuclideanSpace ℂ κ) =>
      finitePiLpComplexOuterEquiv
        (A (finitePiLpComplexOuterEquiv.symm z)))
    (finitePiLpCanonicalComplexificationCLM_id (ι := ι) (κ := κ))
  simpa [finitePiLpCanonicalComplexificationOuterCLM] using h

/-- Any exact real inverse law remains exact after canonical complexification
and explicit transport from the counting-Hilbert outer space to the ordinary
finite function space.  The order of `S` and `T` is retained, so the same
lemma transports both left- and right-inverse laws. -/
theorem finitePiLpCanonicalComplexificationOuterCLM_comp_eq_id
    (S T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (hST : S.comp T = ContinuousLinearMap.id ℝ
      (FinitePiLpField ι (EuclideanSpace ℝ κ))) :
    (finitePiLpCanonicalComplexificationOuterCLM S).comp
        (finitePiLpCanonicalComplexificationOuterCLM T) =
      ContinuousLinearMap.id ℂ (ι → EuclideanSpace ℂ κ) := by
  calc
    (finitePiLpCanonicalComplexificationOuterCLM S).comp
          (finitePiLpCanonicalComplexificationOuterCLM T) =
        finitePiLpCanonicalComplexificationOuterCLM (S.comp T) :=
      (finitePiLpCanonicalComplexificationOuterCLM_comp S T).symm
    _ = finitePiLpCanonicalComplexificationOuterCLM
          (ContinuousLinearMap.id ℝ
            (FinitePiLpField ι (EuclideanSpace ℝ κ))) := by rw [hST]
    _ = ContinuousLinearMap.id ℂ (ι → EuclideanSpace ℂ κ) :=
      finitePiLpCanonicalComplexificationOuterCLM_id

end

end YangMills.RG
