import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Riesz operator of a real bounded bilinear form

Mathlib's basis-free Riesz constructor is stated for bounded sesquilinear
forms.  Over `ℝ`, conjugation is trivial, so an ordinary bounded bilinear form
can be reinterpreted without a cast across ring-hom parameters.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reinterpret a real bounded bilinear form as the sesquilinear form expected
by the Hilbert-space Riesz constructor. -/
def realBilinearToSesq (B : E →L[ℝ] E →L[ℝ] ℝ) :
    E →L⋆[ℝ] E →L[ℝ] ℝ where
  toFun := B
  map_add' x y := B.map_add x y
  map_smul' r x := by
    simpa using B.map_smul r x
  cont := B.continuous

@[simp]
theorem realBilinearToSesq_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    realBilinearToSesq B x = B x := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The canonical continuous operator representing a real bounded bilinear
form under the convention `⟪T x, y⟫ = B x y`. -/
noncomputable def realBilinearRiesz
    (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (realBilinearToSesq B)

@[simp]
theorem inner_realBilinearRiesz
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    inner ℝ (realBilinearRiesz B x) y = B x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (realBilinearToSesq B) x y

end YangMills.RG
