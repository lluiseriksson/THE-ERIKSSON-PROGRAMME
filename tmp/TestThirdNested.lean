import YangMills.RG.BalabanCMP102Eq80SourcePi4ThirdFieldDerivative

open YangMills.RG

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def nestedOfThird
    (L : E [×3]→L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    ((continuousMultilinearCurryRightEquiv' ℝ 1 E
      (E →L[ℝ] ℝ))
      ((continuousMultilinearCurryRightEquiv' ℝ 2 E ℝ) L))

example (L : E [×3]→L[ℝ] ℝ) (a b c : E) :
    nestedOfThird L a b c = L ![a, b, c] := by
  simp [nestedOfThird]

example {T : Type*} [TopologicalSpace T]
    (L : T → E [×3]→L[ℝ] ℝ) (hL : Continuous L) :
    Continuous fun t => nestedOfThird (L t) := by
  unfold nestedOfThird
  fun_prop
