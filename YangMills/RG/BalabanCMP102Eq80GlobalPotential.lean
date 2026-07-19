import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The global CMP102 equation-(80) potential

The primary CMP102 paper, *The variational problem and background fields in
renormalization group method for lattice gauge theories*, defines the
pre-localization higher-order potential by the literal four-term formula

`V(A') = - <H D₃(A'), J> - <A', Δπ H D(A')>`
`        + (1/2) <H D(A'), Δπ H D(A')> + V₀(A' - H D(A'))`.

This file records that formula without fusing its source components and proves
the normalization facts needed later by the radial Taylor construction.  The
linearization `D'(0)` is deliberately arbitrary: the two quadratic pairings
have zero first derivative merely because `D(0) = 0`, while the first and last
terms are killed by the source facts `D₃'(0) = 0` and `V₀'(0) = 0`.

Honest scope: this is the global, pre-localization CMP102 functional.  It is
not a definition of the CMP116 domain activity `V_k(Y, ·)`, it does not choose
the CMP116 residual `V''_k` to be zero, and it is not instantiated into the
equation-(1.42) source split.  The propagator localization, the concrete
`Y`-indexed total/residual dictionary, and estimates (1.36)/(1.43) remain open.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- The literal global higher-order potential printed as equation (80) in
CMP102.  Its six source ingredients remain separately visible in the type. -/
noncomputable def cmp102Eq80GlobalPotential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D D₃ : E → E) (V₀ : E → ℝ)
    (H Δπ : E →L[ℝ] E) (J : E) (A' : E) : ℝ :=
  - inner ℝ (H (D₃ A')) J
  - inner ℝ A' (Δπ (H (D A')))
  + (1 / 2 : ℝ) * inner ℝ (H (D A')) (Δπ (H (D A')))
  + V₀ (A' - H (D A'))

/-- The source component normalizations imply that the equation-(80)
potential vanishes at the origin.  No differentiability is needed. -/
theorem cmp102Eq80GlobalPotential_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D D₃ : E → E) (V₀ : E → ℝ)
    (H Δπ : E →L[ℝ] E) (J : E)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J 0 = 0 := by
  simp [cmp102Eq80GlobalPotential, hD0, hD₃0, hV₀0]

/-- Term-by-term chain rule at the origin.  Notice that the derivative `D'`
is unrestricted: only the value `D(0)=0`, the absence of a linear term in
`D₃`, and the absence of a linear term in `V₀` are consumed. -/
theorem cmp102Eq80GlobalPotential_hasFDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D D₃ : E → E) (V₀ : E → ℝ)
    (H Δπ : E →L[ℝ] E) (J : E)
    (D' : E →L[ℝ] E)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD₃ : HasFDerivAt D₃ (0 : E →L[ℝ] E) 0)
    (hV₀ : HasFDerivAt V₀ (0 : E →L[ℝ] ℝ) 0) :
    HasFDerivAt (cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J)
      (0 : E →L[ℝ] ℝ) 0 := by
  have hHD : HasFDerivAt (fun A => H (D A)) (H.comp D') 0 :=
    H.hasFDerivAt.comp 0 hD
  have hHD₃ : HasFDerivAt (fun A => H (D₃ A)) (0 : E →L[ℝ] E) 0 := by
    simpa using H.hasFDerivAt.comp 0 hD₃
  have hJ : HasFDerivAt (fun _ : E => J) (0 : E →L[ℝ] E) 0 :=
    hasFDerivAt_const (x := (0 : E)) (c := J)
  have hfirst : HasFDerivAt
      (fun A => - inner ℝ (H (D₃ A)) J) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hHD₃.inner ℝ hJ).neg using 1
    ext v
    simp [hD₃0]
  have hid : HasFDerivAt (fun A : E => A) 1 0 :=
    hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E))
  have hΔπHD : HasFDerivAt (fun A => Δπ (H (D A)))
      (Δπ.comp (H.comp D')) 0 := Δπ.hasFDerivAt.comp 0 hHD
  have hsecond : HasFDerivAt
      (fun A => - inner ℝ A (Δπ (H (D A)))) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hid.inner ℝ hΔπHD).neg using 1
    ext v
    simp [hD0]
  have hthirdInner : HasFDerivAt
      (fun A => inner ℝ (H (D A)) (Δπ (H (D A))))
      (0 : E →L[ℝ] ℝ) 0 := by
    convert hHD.inner ℝ hΔπHD using 1
    ext v
    simp [hD0]
  have hthird : HasFDerivAt
      (fun A => (1 / 2 : ℝ) * inner ℝ (H (D A)) (Δπ (H (D A))))
      (0 : E →L[ℝ] ℝ) 0 := by
    simpa using hthirdInner.const_mul (1 / 2 : ℝ)
  have harg : HasFDerivAt (fun A => A - H (D A))
      (1 - H.comp D') 0 := hid.sub hHD
  have hfourth : HasFDerivAt (fun A => V₀ (A - H (D A)))
      (0 : E →L[ℝ] ℝ) 0 := by
    have hV₀arg : HasFDerivAt V₀ (0 : E →L[ℝ] ℝ) (0 - H (D 0)) := by
      simpa [hD0] using hV₀
    simpa only [Function.comp_def] using hV₀arg.comp 0 harg
  convert ((hfirst.add hsecond).add hthird).add hfourth using 1
  · simp

/-- The equation-(80) potential therefore has zero Fréchet derivative at the
origin under the same component hypotheses. -/
theorem fderiv_cmp102Eq80GlobalPotential_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D D₃ : E → E) (V₀ : E → ℝ)
    (H Δπ : E →L[ℝ] E) (J : E)
    (D' : E →L[ℝ] E)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD : HasFDerivAt D D' 0)
    (hD₃ : HasFDerivAt D₃ (0 : E →L[ℝ] E) 0)
    (hV₀ : HasFDerivAt V₀ (0 : E →L[ℝ] ℝ) 0) :
    fderiv ℝ (cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J) 0 = 0 :=
  (cmp102Eq80GlobalPotential_hasFDerivAt_zero
    D D₃ V₀ H Δπ J D' hD0 hD₃0 hD hD₃ hV₀).fderiv

/-- `C²` regularity of the source components propagates to the literal
equation-(80) functional. -/
theorem contDiff_two_cmp102Eq80GlobalPotential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D D₃ : E → E) (V₀ : E → ℝ)
    (H Δπ : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 2 (cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J) := by
  have hHD : ContDiff ℝ 2 (fun A => H (D A)) := H.contDiff.comp hD
  have hHD₃ : ContDiff ℝ 2 (fun A => H (D₃ A)) := H.contDiff.comp hD₃
  have hΔπHD : ContDiff ℝ 2 (fun A => Δπ (H (D A))) :=
    Δπ.contDiff.comp hHD
  have hfirst : ContDiff ℝ 2 (fun A => - inner ℝ (H (D₃ A)) J) :=
    (hHD₃.inner ℝ contDiff_const).neg
  have hsecond : ContDiff ℝ 2
      (fun A => - inner ℝ A (Δπ (H (D A)))) :=
    ((contDiff_id : ContDiff ℝ 2 (fun A : E => A)).inner ℝ hΔπHD).neg
  have hthird : ContDiff ℝ 2
      (fun A => (1 / 2 : ℝ) * inner ℝ (H (D A)) (Δπ (H (D A)))) :=
    contDiff_const.mul (hHD.inner ℝ hΔπHD)
  have hfourth : ContDiff ℝ 2 (fun A => V₀ (A - H (D A))) :=
    hV₀.comp ((contDiff_id : ContDiff ℝ 2 (fun A : E => A)).sub hHD)
  convert ((hfirst.add hsecond).add hthird).add hfourth using 1

/-- A concrete nonzero instance: the equation-(80) functional is not forced
to vanish identically by its normalization interface. -/
theorem cmp102Eq80GlobalPotential_nontrivial_witness :
    cmp102Eq80GlobalPotential
      (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun x : ℝ => x ^ 2)
      (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →L[ℝ] ℝ) 0 1 = 1 := by
  norm_num [cmp102Eq80GlobalPotential]

end

end YangMills.RG
