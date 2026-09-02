import YangMills.RG.BalabanCMP89CenteredUnitCubeTorusQuotient
import YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain
import YangMills.RG.BalabanCMP89Eq248CenteredGreenTorus

/-!
# PRE-VALIDATION: mass-uniform centered-torus model of the full CMP89 (2.46) Green

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module descends the literal two-endpoint (2.46) fine-to-fine integrand
to the centered four-torus on the whole printed mass window, including
`mass = 0`.  Continuity and the face seam are derived internally from the
mass-uniform analytic domain.  The target and source remain separate; this
is not the one-displacement (2.48) Green.

No Fourier coefficient dictionary, finite-grid periodization, generated
regional Green identification, `B0`, `delta0`, window-15 attainment,
terminal field or `TermSource` inhabitant is asserted here.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal full (2.46) fine-to-fine Green on the centered momentum cube.
The negative-momentum convention is the one used by the physical CMP99
coarse base momentum. -/
def cmp89Eq246CenteredFullGreenCube
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) : ℂ :=
  cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
    (fun mu => (cmp89Eq248CenteredCubeMomentum t mu : ℂ)) target source

/-- Continuity of the literal two-endpoint Green on the centered cube,
uniformly on the printed mass window. -/
theorem continuous_cmp89Eq246CenteredFullGreenCube_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    Continuous (cmp89Eq246CenteredFullGreenCube L j mass a target source) := by
  rw [continuous_iff_continuousAt]
  intro t
  let p := cmp89Eq248CenteredCubeMomentum t
  have hp : ∀ mu, |p mu| ≤ Real.pi :=
    abs_cmp89Eq248CenteredCubeMomentum_le_pi t
  have houter : DifferentiableAt ℂ
      (fun z : Fin 4 → ℂ =>
        cmp89Eq246PhysicalFineToFineGreenIntegrand
          L j mass a z target source)
      (fun mu => (p mu : ℂ)) := by
    simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand] using
      (differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius_massUniform
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        (p := p) hp (z := fun mu => (p mu : ℂ))
        (by intro mu; simp) (by intro mu; simpa using hrho)
        (targetEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) target)
        (sourceEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) source))
  have hinnerContinuous : Continuous
      (fun q : CMP89CenteredUnitCube (Fin 4) =>
        fun mu => (cmp89Eq248CenteredCubeMomentum q mu : ℂ)) := by
    exact continuous_pi fun mu =>
      Complex.continuous_ofReal.comp
        ((continuous_const.mul
          (continuous_subtype_val.comp (continuous_apply mu))))
  have hinner : ContinuousAt
      (fun q : CMP89CenteredUnitCube (Fin 4) =>
        fun mu => (cmp89Eq248CenteredCubeMomentum q mu : ℂ)) t :=
    hinnerContinuous.continuousAt
  change ContinuousAt
    (fun q : CMP89CenteredUnitCube (Fin 4) =>
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (fun mu => (cmp89Eq248CenteredCubeMomentum q mu : ℂ))
        target source) t
  simpa only [Function.comp_apply] using houter.continuousAt.comp hinner

/-- The two opposite faces of each centered-cube coordinate give the same
literal full-G value. -/
theorem cmp89Eq246CenteredFullGreenCube_faceSeam_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) (nu : Fin 4) :
    cmp89Eq246CenteredFullGreenCube L j mass a target source
        (Function.update t nu cmp89CenteredUnitLeft) =
      cmp89Eq246CenteredFullGreenCube L j mass a target source
        (Function.update t nu cmp89CenteredUnitRight) := by
  let tRight := Function.update t nu cmp89CenteredUnitRight
  let tLeft := Function.update t nu cmp89CenteredUnitLeft
  let pRight := cmp89Eq248CenteredCubeMomentum tRight
  let pLeft := cmp89Eq248CenteredCubeMomentum tLeft
  have hpRight : ∀ mu, |pRight mu| ≤ Real.pi :=
    abs_cmp89Eq248CenteredCubeMomentum_le_pi tRight
  have hface : pRight nu = -Real.pi := by
    simp [pRight, tRight, cmp89Eq248CenteredCubeMomentum,
      cmp89CenteredUnitRight]
    ring
  have hshift :
      cmp89Eq248PhysicalCoordinatePeriodShift nu
          (fun mu => (pRight mu : ℂ)) =
        fun mu => (pLeft mu : ℂ) := by
    funext mu
    by_cases hmu : mu = nu
    · subst mu
      simp [cmp89Eq248PhysicalCoordinatePeriodShift, pRight, pLeft,
        tRight, tLeft, cmp89Eq248CenteredCubeMomentum,
        cmp89CenteredUnitRight, cmp89CenteredUnitLeft]
      ring
    · simp [cmp89Eq248PhysicalCoordinatePeriodShift, pRight, pLeft,
        tRight, tLeft, cmp89Eq248CenteredCubeMomentum, hmu]
  have hperiod :=
    cmp89Eq246PhysicalFineToFineGreenIntegrand_boundarySeam_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      nu hpRight hface (z := fun mu => (pRight mu : ℂ))
      (by intro mu; simp) (by intro mu; simpa using hrho)
      target source
  simpa [cmp89Eq246CenteredFullGreenCube, tRight, tLeft, pRight, pLeft,
    hshift] using hperiod

/-- Bundled continuous full-G function on the centered cube. -/
def cmp89Eq246CenteredFullGreenCubeContinuous
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) :
    C(CMP89CenteredUnitCube (Fin 4), ℂ) where
  toFun := cmp89Eq246CenteredFullGreenCube L j mass a target source
  continuous_toFun :=
    continuous_cmp89Eq246CenteredFullGreenCube_massUniform
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source

/-- Literal mass-uniform full (2.46) Green descended to the four-torus. -/
def cmp89Eq246CenteredFullGreenTorus
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ) : C(UnitAddTorus (Fin 4), ℂ) :=
  cmp89CenteredUnitCubeLift
    (cmp89Eq246CenteredFullGreenCubeContinuous
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source)
    (cmp89Eq246CenteredFullGreenCube_faceSeam_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source)

/-- Exact pullback of the descended full-G torus function. -/
theorem cmp89Eq246CenteredFullGreenTorus_covering_apply
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) :
    cmp89Eq246CenteredFullGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        target source (cmp89CenteredUnitCubeToTorus t) =
      cmp89Eq246CenteredFullGreenCube L j mass a target source t := by
  have h := cmp89CenteredUnitCubeLift_comp_covering
    (cmp89Eq246CenteredFullGreenCubeContinuous
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source)
    (cmp89Eq246CenteredFullGreenCube_faceSeam_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass target source)
  exact DFunLike.congr_fun h t

end

end YangMills.RG
