import YangMills.RG.BalabanCMP89Eq246FineToFineGreenOneCoordinateContourShift
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloorMassUniform

/-!
# Mass-uniform analytic domain for the full CMP89 (2.46) kernel

The already sealed central-denominator floor is uniform on the literal mass
window and does not require `0 < mass`.  This module threads that stronger
fact through the complete (2.46) finite-solver domain, boundary seam,
holomorphy and one-coordinate contour shift.  In particular it admits the
physical specialization `mass = 0`; it does not identify the Fourier kernel
with the generated regional Green, prove periodization, produce `B0` or
`delta0`, attain window 15, discharge a terminal row, or inhabit `TermSource`.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The common polistrip constructs the complete (2.46) solver domain on the
whole printed mass window, including `mass = 0`. -/
theorem cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    CMP89Eq246FullSolutionDomain 4 L j mass a z := by
  have hfine : ∀ m : CMP89Eq246AliasIndex 4 L j,
      m ≠ cmp89Eq249CentralAliasIndex 4 L j →
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z m ≠ 0 := by
    intro m hm
    have hm0 : m.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hm0
      apply hm
      apply Subtype.ext
      exact hm0
    have hmErase :
        m.1 ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
          (cmp89Eq249ZeroAlias 4) := Finset.mem_erase.mpr ⟨hm0, m.2⟩
    exact cmp89Eq251NoncentralFineSymbol_ne_zero_of_commonRadius
      hrho hradius hmErase hp hreal himag
  have hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z ≠ 0 :=
    cmp89Eq249CentralStabilizedAliasDenominator_ne_zero_massUniform
      ha hrho hradius hmass hdenWindow hp hreal himag hamplitude
  have hpair : cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 :=
    cmp89Eq249CentralEntireAveragePair_ne_zero
      hrho hpairWindow hp hreal himag
  exact ⟨hfine, hstabilized,
    cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 L j z hpair⟩

/-- The complete fine-to-fine integrand has the physical Brillouin boundary
seam uniformly on the mass window. -/
theorem cmp89Eq246PhysicalFineToFineGreenIntegrand_boundarySeam_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (target source : Fin 4 → ℤ) :
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift nu z) target source =
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        z target source := by
  let pShift : Fin 4 → ℝ := fun k => if k = nu then Real.pi else p k
  have hpShift : ∀ k, |pShift k| ≤ Real.pi := by
    intro k
    by_cases hk : k = nu
    · subst k
      simp [pShift, abs_of_pos Real.pi_pos]
    · simpa [pShift, hk] using hp k
  have hrealShift : ∀ k,
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z k).re = pShift k := by
    intro k
    by_cases hk : k = nu
    · subst k
      simp [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply,
        pShift, hreal nu, hface]
      ring
    · simp [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply,
        pShift, hk, hreal k]
  have himagShift : ∀ k,
      |(cmp89Eq248PhysicalCoordinatePeriodShift nu z k).im| ≤ rho := by
    intro k
    by_cases hk : k = nu
    · subst k
      simpa [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply]
        using himag nu
    · simpa [cmp89Eq248PhysicalCoordinatePeriodShift, Pi.single_apply, hk]
        using himag k
  have baseDomain : CMP89Eq246FullSolutionDomain 4 L j mass a z :=
    cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        hp hreal himag
  have shiftedDomain : CMP89Eq246FullSolutionDomain 4 L j mass a
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z) :=
    cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        hpShift hrealShift himagShift
  exact cmp89Eq246PhysicalFineToFineGreenIntegrand_periodShift
    L j mass a nu z target source baseDomain shiftedDomain

/-- The full fine-to-fine integrand is holomorphic throughout the common
polistrip on the whole printed mass window. -/
theorem differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    {targetEndpoint sourceEndpoint : Fin 4 → ℝ} :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 L j mass a w
        targetEndpoint sourceEndpoint) z := by
  have hdomain := cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass hp hreal himag
  exact differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand
    hdomain.fine hdomain.stabilized hdomain.row

/-- One coordinate of the physical full-G integral may be displaced through
the common strip at `mass = 0` as well as at positive mass. -/
theorem intervalIntegral_cmp89Eq246PhysicalFineToFineGreenIntegrand_coordinateShift_massUniform
    {L j : ℕ} [NeZero L] {mass a rho eta : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (heta : |eta| ≤ rho) (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho) (hnuImag : (z nu).im = 0)
    (target source : Fin 4 → ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (cmp89Eq251PhysicalCoordinateLine nu z (x : ℂ)) target source) =
      ∫ x : ℝ in 0..2 * Real.pi,
        cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
          (cmp89Eq251PhysicalCoordinateLine nu z
            ((x : ℂ) + eta * Complex.I)) target source := by
  let f : ℂ → ℂ := fun w =>
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
      (cmp89Eq251PhysicalCoordinateLine nu z w) target source
  have himag_of_mem (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) eta) :
      ∀ k, |(cmp89Eq251PhysicalCoordinateLine nu z
        (y * Complex.I) k).im| ≤ rho := by
    intro k
    by_cases hk : k = nu
    · subst k
      have hyAbs : |y| ≤ |eta| := by
        simpa using Set.abs_sub_left_of_mem_uIcc hy
      simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
        hnuImag] using hyAbs.trans heta
    · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
        using himag k
  have hboundary : ∀ y ∈ Set.uIcc (0 : ℝ) eta,
      f (((2 * Real.pi : ℝ) : ℂ) + y * Complex.I) =
        f (y * Complex.I) := by
    intro y hy
    have hrealY : ∀ k,
        (cmp89Eq251PhysicalCoordinateLine nu z
          (y * Complex.I) k).re = p k := by
      intro k
      by_cases hk : k = nu
      · subst k
        simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hreal nu]
      · simp [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k]
    have hseam :=
      cmp89Eq246PhysicalFineToFineGreenIntegrand_boundarySeam_massUniform
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        nu hp hface hrealY (himag_of_mem y hy) target source
    unfold f
    convert hseam using 1
    exact congrArg
      (fun q : Fin 4 → ℂ =>
        cmp89Eq246PhysicalFineToFineGreenIntegrand
          L j mass a q target source)
      (cmp89Eq251PhysicalCoordinateLine_two_pi_add nu z
        (y * Complex.I))
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc 0 (2 * Real.pi) ×ℂ Set.uIcc 0 eta) := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have hx : 0 ≤ w.re ∧ w.re ≤ 2 * Real.pi := by
      have hx' := hw.1
      rw [Set.uIcc_of_le (mul_nonneg (by norm_num) Real.pi_pos.le)] at hx'
      exact hx'
    have hyAbs : |w.im| ≤ |eta| := by
      simpa using Set.abs_sub_left_of_mem_uIcc hw.2
    let pw : Fin 4 → ℝ := fun k =>
      (cmp89Eq251PhysicalCoordinateLine nu z w k).re
    have hpw : ∀ k, |pw k| ≤ Real.pi := by
      intro k
      by_cases hk : k = nu
      · subst k
        have hbounds : -Real.pi ≤ -Real.pi + w.re ∧
            -Real.pi + w.re ≤ Real.pi := by
          constructor <;> linarith [Real.pi_pos]
        rw [abs_le]
        simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hreal nu, hface] using hbounds
      · simpa [pw, cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk,
          hreal k] using hp k
    have himagW : ∀ k,
        |(cmp89Eq251PhysicalCoordinateLine nu z w k).im| ≤ rho := by
      intro k
      by_cases hk : k = nu
      · subst k
        simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply,
          hnuImag] using hyAbs.trans heta
      · simpa [cmp89Eq251PhysicalCoordinateLine, Pi.single_apply, hk]
          using himag k
    have houter : DifferentiableAt ℂ
        (fun q : Fin 4 → ℂ =>
          cmp89Eq246PhysicalFineToFineGreenIntegrand
            L j mass a q target source)
        (cmp89Eq251PhysicalCoordinateLine nu z w) := by
      simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand] using
        (differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius_massUniform
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hdenWindow hpairWindow hmass
          (p := pw) hpw
          (z := cmp89Eq251PhysicalCoordinateLine nu z w)
          (by intro k; rfl) himagW
          (targetEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) target)
          (sourceEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) source))
    have hinner : DifferentiableAt ℂ
        (cmp89Eq251PhysicalCoordinateLine nu z) w := by
      simpa [cmp89Eq251PhysicalCoordinateLine] using
        ((hasFDerivAt_single (𝕜 := ℂ) (i := nu) w).const_add z).differentiableAt
    simpa [f] using (houter.comp w hinner).differentiableWithinAt
  exact intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
    f (2 * Real.pi) eta hboundary hdiff

end

end YangMills.RG
