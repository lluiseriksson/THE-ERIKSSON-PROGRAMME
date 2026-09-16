import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainNormalization
import Mathlib.Analysis.Analytic.IteratedFDeriv

open scoped RealInnerProductSpace
namespace YangMills.RG
noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

theorem test_joint
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2) := by
  unfold cmp102Eq80GlobalPotential
  have hHD : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hHD₃ : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        p.1 (D₃ p.2)) :=
    contDiff_fst.clm_apply (hD₃.comp contDiff_snd)
  have hΔHD : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        Δπ (p.1 (D p.2))) :=
    Δπ.contDiff.comp hHD
  exact
    (((hHD₃.inner ℝ contDiff_const).neg.add
      ((contDiff_snd.inner ℝ hΔHD).neg)).add
      (contDiff_const.mul (hHD.inner ℝ hΔHD))).add
      (hV₀.comp (contDiff_snd.sub hHD))

theorem test_partial
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (D' : PhysicalEndomorphism M Q Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD' : HasFDerivAt D D' 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (H : PhysicalEndomorphism M Q Nc)
    (a : PhysicalField M Q Nc) :
    fderiv ℝ
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
      (H, 0) (0, a) = 0 := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hF : ContDiff ℝ ⊤ F :=
    test_joint D D₃ V₀ Δπ J hD hD₃ hV₀
  have hpath : HasFDerivAt (fun x : PhysicalField M Q Nc => (H, x))
      ((0 : PhysicalField M Q Nc →L[ℝ] PhysicalEndomorphism M Q Nc).prod
        (1 : PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc)) 0 :=
    (hasFDerivAt_const (x := (0 : PhysicalField M Q Nc)) H).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : PhysicalField M Q Nc)))
  have hcomp :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      (0 : PhysicalField M Q Nc) hpath
  have hslice :=
    cmp102Eq80GlobalPotential_hasFDerivAt_zero
      D D₃ V₀ H Δπ J D' hD0 hD₃0 hD' hD₃' hV₀'
  have heq := hcomp.unique hslice
  have heval := congrArg (fun T => T a) heq
  simpa [F] using heval

end
end YangMills.RG
