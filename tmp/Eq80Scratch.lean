import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace

#check hasFDerivAt_const
#check ContinuousLinearMap.hasFDerivAt
#check HasFDerivAt.inner
#check HasFDerivAt.comp
#check HasFDerivAt.sub
#check HasFDerivAt.add
#check HasFDerivAt.const_mul
#check HasFDerivAt.smul_const

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable def eq80
    (D D3 : E → E) (V0 : E → ℝ)
    (H Delta : E →L[ℝ] E) (J : E) (A : E) : ℝ :=
  - inner ℝ (H (D3 A)) J
  - inner ℝ A (Delta (H (D A)))
  + (1 / 2 : ℝ) * inner ℝ (H (D A)) (Delta (H (D A)))
  + V0 (A - H (D A))

theorem eq80_zero
    (D D3 : E → E) (V0 : E → ℝ)
    (H Delta : E →L[ℝ] E) (J : E)
    (hD0 : D 0 = 0) (hD30 : D3 0 = 0) (hV00 : V0 0 = 0) :
    eq80 D D3 V0 H Delta J 0 = 0 := by
  simp [eq80, hD0, hD30, hV00]

theorem eq80_hasFDerivAt_zero
    (D D3 : E → E) (V0 : E → ℝ)
    (H Delta : E →L[ℝ] E) (J : E)
    (D' : E →L[ℝ] E)
    (hD0 : D 0 = 0) (hD30 : D3 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD3 : HasFDerivAt D3 (0 : E →L[ℝ] E) 0)
    (hV0 : HasFDerivAt V0 (0 : E →L[ℝ] ℝ) 0) :
    HasFDerivAt (eq80 D D3 V0 H Delta J) (0 : E →L[ℝ] ℝ) 0 := by
  have hHD : HasFDerivAt (fun A => H (D A)) (H.comp D') 0 :=
    H.hasFDerivAt.comp 0 hD
  have hHD3 : HasFDerivAt (fun A => H (D3 A)) (0 : E →L[ℝ] E) 0 := by
    simpa using H.hasFDerivAt.comp 0 hD3
  have hJ : HasFDerivAt (fun _ : E => J) (0 : E →L[ℝ] E) 0 := hasFDerivAt_const (x := (0 : E)) (c := J)
  have h1 : HasFDerivAt (fun A => - inner ℝ (H (D3 A)) J) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hHD3.inner ℝ hJ).neg using 1
    ext v
    simp [hD30]
  have hid : HasFDerivAt (fun A : E => A) 1 0 := hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E))
  have hDeltaHD : HasFDerivAt (fun A => Delta (H (D A)))
      (Delta.comp (H.comp D')) 0 := Delta.hasFDerivAt.comp 0 hHD
  have h2 : HasFDerivAt (fun A => - inner ℝ A (Delta (H (D A)))) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hid.inner ℝ hDeltaHD).neg using 1
    ext v
    simp [hD0]
  have h3inner : HasFDerivAt
      (fun A => inner ℝ (H (D A)) (Delta (H (D A)))) (0 : E →L[ℝ] ℝ) 0 := by
    convert hHD.inner ℝ hDeltaHD using 1
    ext v
    simp [hD0]
  have h3 : HasFDerivAt
      (fun A => (1 / 2 : ℝ) * inner ℝ (H (D A)) (Delta (H (D A)))) (0 : E →L[ℝ] ℝ) 0 := by
    simpa using h3inner.const_mul (1 / 2 : ℝ)
  have harg : HasFDerivAt (fun A => A - H (D A))
      (1 - H.comp D') 0 := hid.sub hHD
  have h4 : HasFDerivAt (fun A => V0 (A - H (D A))) (0 : E →L[ℝ] ℝ) 0 := by
    have hV0arg : HasFDerivAt V0 (0 : E →L[ℝ] ℝ) (0 - H (D 0)) := by
      simpa [hD0] using hV0
    simpa only [Function.comp_def] using hV0arg.comp 0 harg
  convert ((h1.add h2).add h3).add h4 using 1
  · simp

theorem eq80_contDiff_two
    (D D3 : E → E) (V0 : E → ℝ)
    (H Delta : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ 2 D) (hD3 : ContDiff ℝ 2 D3)
    (hV0 : ContDiff ℝ 2 V0) :
    ContDiff ℝ 2 (eq80 D D3 V0 H Delta J) := by
  have hHD : ContDiff ℝ 2 (fun A => H (D A)) := H.contDiff.comp hD
  have hHD3 : ContDiff ℝ 2 (fun A => H (D3 A)) := H.contDiff.comp hD3
  have hDeltaHD : ContDiff ℝ 2 (fun A => Delta (H (D A))) :=
    Delta.contDiff.comp hHD
  have h1 : ContDiff ℝ 2 (fun A => - inner ℝ (H (D3 A)) J) :=
    (hHD3.inner ℝ contDiff_const).neg
  have h2 : ContDiff ℝ 2 (fun A => - inner ℝ A (Delta (H (D A)))) :=
    ((contDiff_id : ContDiff ℝ 2 (fun A : E => A)).inner ℝ hDeltaHD).neg
  have h3 : ContDiff ℝ 2
      (fun A => (1 / 2 : ℝ) * inner ℝ (H (D A)) (Delta (H (D A)))) :=
    contDiff_const.mul (hHD.inner ℝ hDeltaHD)
  have h4 : ContDiff ℝ 2 (fun A => V0 (A - H (D A))) :=
    hV0.comp ((contDiff_id : ContDiff ℝ 2 (fun A : E => A)).sub hHD)
  convert ((h1.add h2).add h3).add h4 using 1

end
