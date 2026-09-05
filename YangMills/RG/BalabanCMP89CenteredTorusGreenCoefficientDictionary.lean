/-
SEALED SOURCE-SPECIFIC BRICK -- COMPILER-VERIFIED.

This scratch file states the exact G23.4 coefficient dictionary.  It builds
the centered-cube representative only for points in the literal translated
Brillouin cube, proves the pointwise physical identity there, promotes it to
an almost-everywhere identity for the restricted source measure, and finally
identifies the torus Fourier coefficient with the repository's literal
normalized fine-lattice stabilized Green at the positive affine residue.

No arbitrary periodic endpoint family, global representative, Green bound,
`B0`, window-15 attainment or terminal field is accepted or asserted.
-/

import YangMills.RG.BalabanCMP89Eq248CenteredGreenTorus
import YangMills.RG.BalabanCMP89NormalizedBrillouinToTorusMeasure
import YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase
import YangMills.RG.BalabanCMP89Eq248FineLatticeNormalizedFourierGreen


namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The literal translated four-dimensional Brillouin cube supporting the
repository's source measure. -/
def cmp89Eq249PhysicalBrillouinCube : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun _ : Fin 4 => Set.Ioc 0 (2 * Real.pi)

/-- The centered unit-cube representative of a point in the physical
Brillouin cube.  Its value is `1/2 - x/(2*pi)` coordinatewise. -/
def cmp89PhysicalBrillouinCenteredRepresentative
    (x : Fin 4 → ℝ) (hx : x ∈ cmp89Eq249PhysicalBrillouinCube) :
    CMP89CenteredUnitCube (Fin 4) :=
  fun mu => ⟨(1 / 2 : ℝ) - (2 * Real.pi)⁻¹ * x mu, by
    have hxmu : x mu ∈ Set.Ioc 0 (2 * Real.pi) := hx mu (by simp)
    have htwoPi : 0 < (2 * Real.pi : ℝ) :=
      mul_pos (by norm_num) Real.pi_pos
    constructor
    · have := (inv_mul_le_one₀ htwoPi).2 hxmu.2
      linarith
    · have hnonneg : 0 ≤ (2 * Real.pi)⁻¹ * x mu :=
        mul_nonneg (inv_nonneg.mpr htwoPi.le) hxmu.1.le
      linarith⟩

/-- The centered representative covers exactly the normalized physical
Brillouin point on the torus. -/
theorem cmp89CenteredRepresentative_toTorus
    (x : Fin 4 → ℝ) (hx : x ∈ cmp89Eq249PhysicalBrillouinCube) :
    cmp89CenteredUnitCubeToTorus
        (cmp89PhysicalBrillouinCenteredRepresentative x hx) =
      cmp89PhysicalBrillouinToUnitAddTorus x := by
  rfl

/-- The negative momentum of the centered representative is the literal
translated physical Brillouin momentum. -/
theorem cmp89CenteredRepresentative_momentum
    (x : Fin 4 → ℝ) (hx : x ∈ cmp89Eq249PhysicalBrillouinCube) :
    cmp89Eq248CenteredCubeMomentum
        (cmp89PhysicalBrillouinCenteredRepresentative x hx) =
      cmp89Eq251PhysicalBrillouinParameter x := by
  funext mu
  unfold cmp89Eq248CenteredCubeMomentum
    cmp89PhysicalBrillouinCenteredRepresentative
    cmp89Eq251PhysicalBrillouinParameter
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  field_simp [htwoPi]
  ring

/-- Pointwise coefficient identity on the actual source cube.  The torus
character and descended Green land at the literal physical Green with
positive affine endpoint `u + L^j*n`. -/
theorem cmp89_mFourier_mul_centeredGreen_physicalBrillouin
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u n : Fin 4 → ℤ) (x : Fin 4 → ℝ)
    (hx : x ∈ cmp89Eq249PhysicalBrillouinCube) :
    UnitAddTorus.mFourier (-n)
          (cmp89PhysicalBrillouinToUnitAddTorus x) *
        cmp89Eq248CenteredGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hwindow hmass u
          (cmp89PhysicalBrillouinToUnitAddTorus x) =
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹)
          (fun mu => u mu + ((L ^ j : ℕ) : ℤ) * n mu)) := by
  let t := cmp89PhysicalBrillouinCenteredRepresentative x hx
  have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hcover := cmp89Eq248CenteredGreenTorus_covering_apply
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hwindow hmass u t
  rw [← cmp89CenteredRepresentative_toTorus x hx, hcover]
  unfold cmp89Eq248CenteredGreenCube
  rw [cmp89CenteredRepresentative_momentum]
  have htorus :
      (fun mu => (((t mu).1 : ℝ) : UnitAddCircle)) =
        cmp89CenteredUnitCubeToTorus t := by
    rfl
  have hreal :
      cmp89Eq248CenteredCubeMomentum t =
        cmp89Eq251PhysicalBrillouinParameter x := by
    simpa only [t] using cmp89CenteredRepresentative_momentum x hx
  have hmom :
      cmp89Eq248NegativeTwoPiTorusMomentum (fun mu => (t mu).1) =
        fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ) := by
    funext mu
    have hmu := congrFun hreal mu
    calc
      cmp89Eq248NegativeTwoPiTorusMomentum (fun mu => (t mu).1) mu =
          (cmp89Eq248CenteredCubeMomentum t mu : ℂ) := by
        unfold cmp89Eq248NegativeTwoPiTorusMomentum
          cmp89Eq248CenteredCubeMomentum
        push_cast
        ring
      _ = (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ) := by
        exact congrArg (fun z : ℝ => (z : ℂ)) hmu
  have hphase :=
    cmp89UnitAddTorus_mFourier_neg_mul_stabilizedGreen_eq_affineResidue
      (L := L) (j := j) hLj mass a n u (fun mu => (t mu).1)
  rw [htorus, hmom] at hphase
  simpa [cmp89Eq249FineLatticeSpacing, Nat.cast_pow] using hphase

/-- The pointwise dictionary holds almost everywhere for the literal source
measure.  Boundary and off-cube values are not promoted to a global identity.
-/
theorem cmp89_ae_mFourier_mul_centeredGreen_physicalBrillouin
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u n : Fin 4 → ℤ) :
    ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      UnitAddTorus.mFourier (-n)
            (cmp89PhysicalBrillouinToUnitAddTorus x) *
          cmp89Eq248CenteredGreenTorus
            (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
            ha hrho hamplitude hradius hwindow hmass u
            (cmp89PhysicalBrillouinToUnitAddTorus x) =
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a
          (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L ^ j : ℕ) : ℝ)⁻¹)
            (fun mu => u mu + ((L ^ j : ℕ) : ℤ) * n mu)) := by
  have hmeasure :
      cmp89Eq249FourDimensionalBrillouinMeasure =
        (volume : Measure (Fin 4 → ℝ)).restrict
          cmp89Eq249PhysicalBrillouinCube := by
    unfold cmp89Eq249FourDimensionalBrillouinMeasure
      cmp89Eq249PhysicalBrillouinCube
    rw [volume_pi, Measure.restrict_pi_pi]
    have htwoPi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    simp only [Set.uIoc_of_le htwoPi]
  have hcube : MeasurableSet cmp89Eq249PhysicalBrillouinCube := by
    exact MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ =>
      measurableSet_Ioc
  have hmem :
      ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
        x ∈ cmp89Eq249PhysicalBrillouinCube := by
    rw [hmeasure]
    exact ae_restrict_mem hcube
  filter_upwards [hmem] with x hx
  exact cmp89_mFourier_mul_centeredGreen_physicalBrillouin
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hwindow hmass u n x hx

/-- Exact G23.4 coefficient dictionary.  The Mathlib torus Fourier
coefficient of the literal descended Green is the repository's physical
normalized Green at the positive affine residue. -/
theorem cmp89_mFourierCoeff_centeredGreen_eq_normalizedFineGreen
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (u n : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (cmp89Eq248CenteredGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hwindow hmass u) n =
      cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
        (fun mu => u mu + ((L ^ j : ℕ) : ℤ) * n mu) := by
  let f : C(UnitAddTorus (Fin 4), ℂ) :=
    UnitAddTorus.mFourier (-n) *
      cmp89Eq248CenteredGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass u
  have htransport := integral_unitAddTorus_eq_cmp89NormalizedBrillouin f
  have hae := cmp89_ae_mFourier_mul_centeredGreen_physicalBrillouin
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hwindow hmass u n
  have htransport_mul :
      (∫ t, UnitAddTorus.mFourier (-n) t *
          cmp89Eq248CenteredGreenTorus
            (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
            ha hrho hamplitude hradius hwindow hmass u t
          ∂(Measure.pi fun _ : Fin 4 => AddCircle.haarAddCircle)) =
        cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => UnitAddTorus.mFourier (-n)
              (cmp89PhysicalBrillouinToUnitAddTorus x) *
            cmp89Eq248CenteredGreenTorus
              (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
              ha hrho hamplitude hradius hwindow hmass u
              (cmp89PhysicalBrillouinToUnitAddTorus x)) := by
    have hcircle :
        (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa using
        (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    simpa [f, smul_eq_mul, MeasureTheory.volume_pi, hcircle] using htransport
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  change (∫ t, UnitAddTorus.mFourier (-n) t *
      cmp89Eq248CenteredGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass u t
      ∂(Measure.pi fun _ : Fin 4 => AddCircle.haarAddCircle)) = _
  refine htransport_mul.trans ?_
  unfold cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  congr 1
  exact integral_congr_ae (by
    simpa [f, smul_eq_mul, cmp89Eq249FineLatticeSpacing, Nat.cast_pow] using hae)

end

end YangMills.RG
