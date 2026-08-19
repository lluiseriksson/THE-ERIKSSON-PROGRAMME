/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file specializes the future centered-cube quotient to the
literal mass-uniform stabilized Green endpoint.  It derives continuity and
the coordinate face seam internally; neither is accepted as caller data.

No finite sample dictionary, Fourier coefficient, Green bound, `B0`,
window-15 attainment or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89CenteredUnitCubeTorusQuotient
import YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy
import YangMills.RG.BalabanCMP89CenteredTorusFourierPhase

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

noncomputable section

/-- Literal real momentum on the centered cube in the negative convention
used by the physical CMP99 coarse base momentum. -/
def cmp89Eq248CenteredCubeMomentum
    (t : CMP89CenteredUnitCube (Fin 4)) : Fin 4 → ℝ :=
  fun mu => -2 * Real.pi * (t mu).1

/-- Literal mass-uniform stabilized Green endpoint on the centered cube. -/
def cmp89Eq248CenteredGreenCube
    (L j : ℕ) [NeZero L] (mass a : ℝ) (endpointU : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) : ℂ :=
  cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
    (fun mu => (cmp89Eq248CenteredCubeMomentum t mu : ℂ))
    (cmp89Eq249PhysicalFineLatticeDisplacement
      (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)

/-- Every centered-cube momentum lies in the literal real Brillouin cube. -/
theorem abs_cmp89Eq248CenteredCubeMomentum_le_pi
    (t : CMP89CenteredUnitCube (Fin 4)) (mu : Fin 4) :
    |cmp89Eq248CenteredCubeMomentum t mu| ≤ Real.pi := by
  have htLower := (t mu).property.1
  have htUpper := (t mu).property.2
  unfold cmp89Eq248CenteredCubeMomentum
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_pos]

/-- Continuity of the physical centered-cube Green is derived from the
mass-uniform complete-polydisc producer. -/
theorem continuous_cmp89Eq248CenteredGreenCube
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) :
    Continuous (cmp89Eq248CenteredGreenCube L j mass a endpointU) := by
  rw [continuous_iff_continuousAt]
  intro t
  let p := cmp89Eq248CenteredCubeMomentum t
  have hp : ∀ mu, |p mu| ≤ Real.pi :=
    abs_cmp89Eq248CenteredCubeMomentum_le_pi t
  have houter :=
    continuousAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_real_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass hp
      (endpointDisplacement :=
        cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) endpointU)
  have hinner : ContinuousAt
      (fun q : CMP89CenteredUnitCube (Fin 4) =>
        cmp89Eq248CenteredCubeMomentum q) t := by
    fun_prop
  simpa [cmp89Eq248CenteredGreenCube, p] using
    houter.comp hinner

/-- Replacing a centered-cube coordinate by its two opposite faces leaves
the literal Green value unchanged.  The proof visibly starts from the upper
cube face, whose negative momentum is `-pi`, and shifts it to `+pi`. -/
theorem cmp89Eq248CenteredGreenCube_faceSeam
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) (nu : Fin 4) :
    cmp89Eq248CenteredGreenCube L j mass a endpointU
        (Function.update t nu cmp89CenteredUnitLeft) =
      cmp89Eq248CenteredGreenCube L j mass a endpointU
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
      push_cast
      ring
    · simp [cmp89Eq248PhysicalCoordinatePeriodShift, pRight, pLeft,
        tRight, tLeft, cmp89Eq248CenteredCubeMomentum, hmu]
  have hperiod :=
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_boundarySeam_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass nu hpRight hface
      (z := fun mu => (pRight mu : ℂ))
      (by intro mu; simp)
      (by intro mu; simpa using hrho)
      endpointU
  simpa [cmp89Eq248CenteredGreenCube, tRight, tLeft, pRight, pLeft,
    hshift] using hperiod

/-- Bundled continuous centered-cube Green. -/
def cmp89Eq248CenteredGreenCubeContinuous
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) :
    C(CMP89CenteredUnitCube (Fin 4), ℂ) where
  toFun := cmp89Eq248CenteredGreenCube L j mass a endpointU
  continuous_toFun :=
    continuous_cmp89Eq248CenteredGreenCube ha hrho hamplitude hradius
      hwindow hmass endpointU

/-- Literal stabilized Green descended to the four-torus by the internally
derived face seam. -/
def cmp89Eq248CenteredGreenTorus
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ) : C(UnitAddTorus (Fin 4), ℂ) :=
  cmp89CenteredUnitCubeLift
    (cmp89Eq248CenteredGreenCubeContinuous
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius
      hwindow hmass endpointU)
    (cmp89Eq248CenteredGreenCube_faceSeam
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius
      hwindow hmass endpointU)

/-- Exact pullback of the descended torus Green to the centered cube. -/
theorem cmp89Eq248CenteredGreenTorus_covering_apply
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (endpointU : Fin 4 → ℤ)
    (t : CMP89CenteredUnitCube (Fin 4)) :
    cmp89Eq248CenteredGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass
        endpointU (cmp89CenteredUnitCubeToTorus t) =
      cmp89Eq248CenteredGreenCube L j mass a endpointU t := by
  have h := cmp89CenteredUnitCubeLift_comp_covering
    (cmp89Eq248CenteredGreenCubeContinuous
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius
      hwindow hmass endpointU)
    (cmp89Eq248CenteredGreenCube_faceSeam
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius
      hwindow hmass endpointU)
  exact DFunLike.congr_fun h t

end

end YangMills.RG
