import YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenTorus
import YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientDictionary

/-!
# PRE-VALIDATION: full CMP89 (2.46) centered-torus coefficient dictionary

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module keeps the two fine endpoints of the full (2.46) Green separate.
The negative torus character is pushed through the literal output-alias sum,
where it shifts only the target endpoint by `L^j * n`; the point-source
endpoint is unchanged.  The resulting pointwise identity is transported
through the literal Brillouin measure to identify the actual torus Fourier
coefficient with the normalized full-G kernel on the affine target fibre.

No arbitrary coefficient family, finite-grid periodization, generated
regional Green identification, `B0`, `delta0`, window-15 attainment,
terminal field or `TermSource` inhabitant is accepted or asserted.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The negative torus character shifts only the output endpoint of the
literal full (2.46) alias solution.  The source endpoint and every alias
solution coefficient remain unchanged. -/
theorem cmp89UnitAddTorus_mFourier_neg_mul_stabilizedFineToFineGreen_eq_affineTarget
    {d L j M : ℕ} [NeZero L] (hM : 0 < M) (mass a : ℝ)
    (n target : Fin d → ℤ) (sourceEndpoint : Fin d → ℝ)
    (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
          (fun mu => ((t mu : ℝ) : UnitAddCircle)) *
        cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a
          (cmp89Eq248NegativeTwoPiTorusMomentum t)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            ((M : ℝ)⁻¹) target)
          sourceEndpoint =
      cmp89Eq246StabilizedFineToFineGreenIntegrand d L j mass a
        (cmp89Eq248NegativeTwoPiTorusMomentum t)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          ((M : ℝ)⁻¹) (fun mu => target mu + (M : ℤ) * n mu))
        sourceEndpoint := by
  unfold cmp89Eq246StabilizedFineToFineGreenIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_assoc,
    cmp89UnitAddTorus_mFourier_neg_mul_aliasFinePhase_eq_affineResiduePhase
      hM]

/-- Pointwise full-G coefficient identity on the literal translated
Brillouin cube. -/
theorem cmp89_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source n : Fin 4 → ℤ) (x : Fin 4 → ℝ)
    (hx : x ∈ cmp89Eq249PhysicalBrillouinCube) :
    UnitAddTorus.mFourier (-n)
          (cmp89PhysicalBrillouinToUnitAddTorus x) *
        cmp89Eq246CenteredFullGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hdenWindow hpairWindow hmass
          target source (cmp89PhysicalBrillouinToUnitAddTorus x) =
      cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
        (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
        (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * n mu) source := by
  let t := cmp89PhysicalBrillouinCenteredRepresentative x hx
  have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hcover := cmp89Eq246CenteredFullGreenTorus_covering_apply
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass
    target source t
  rw [← cmp89CenteredRepresentative_toTorus x hx, hcover]
  unfold cmp89Eq246CenteredFullGreenCube
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
    cmp89UnitAddTorus_mFourier_neg_mul_stabilizedFineToFineGreen_eq_affineTarget
      (L := L) (j := j) hLj mass a n target
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) source)
      (fun mu => (t mu).1)
  rw [htorus, hmom] at hphase
  simpa [cmp89Eq246PhysicalFineToFineGreenIntegrand,
    cmp89Eq249FineLatticeSpacing, Nat.cast_pow] using hphase

/-- The pointwise full-G dictionary holds almost everywhere for the literal
Brillouin source measure. -/
theorem cmp89_ae_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source n : Fin 4 → ℤ) :
    ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure,
      UnitAddTorus.mFourier (-n)
            (cmp89PhysicalBrillouinToUnitAddTorus x) *
          cmp89Eq246CenteredFullGreenTorus
            (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
            ha hrho hamplitude hradius hdenWindow hpairWindow hmass
            target source (cmp89PhysicalBrillouinToUnitAddTorus x) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
          (fun mu => (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ))
          (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * n mu) source := by
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
  exact cmp89_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hrho hamplitude hradius hdenWindow hpairWindow hmass
    target source n x hx

/-- Exact full-G coefficient dictionary.  The torus coefficient is the
literal normalized fine-to-fine Green with only its target shifted along the
positive affine residue fibre. -/
theorem cmp89_mFourierCoeff_centeredFullGreen_eq_normalizedFineToFineGreen_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source n : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (cmp89Eq246CenteredFullGreenTorus
          (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
          ha hrho hamplitude hradius hdenWindow hpairWindow hmass
          target source) n =
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
        (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * n mu) source := by
  let f : C(UnitAddTorus (Fin 4), ℂ) :=
    UnitAddTorus.mFourier (-n) *
      cmp89Eq246CenteredFullGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        target source
  have htransport := integral_unitAddTorus_eq_cmp89NormalizedBrillouin f
  have hae :=
    cmp89_ae_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass
      target source n
  have htransport_mul :
      (∫ t, UnitAddTorus.mFourier (-n) t *
          cmp89Eq246CenteredFullGreenTorus
            (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
            ha hrho hamplitude hradius hdenWindow hpairWindow hmass
            target source t
          ∂(Measure.pi fun _ : Fin 4 => AddCircle.haarAddCircle)) =
        cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => UnitAddTorus.mFourier (-n)
              (cmp89PhysicalBrillouinToUnitAddTorus x) *
            cmp89Eq246CenteredFullGreenTorus
              (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
              ha hrho hamplitude hradius hdenWindow hpairWindow hmass
              target source (cmp89PhysicalBrillouinToUnitAddTorus x)) := by
    have hcircle :
        (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa using
        (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    simpa [f, smul_eq_mul, MeasureTheory.volume_pi, hcircle] using htransport
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  change (∫ t, UnitAddTorus.mFourier (-n) t *
      cmp89Eq246CenteredFullGreenTorus
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hdenWindow hpairWindow hmass
        target source t
      ∂(Measure.pi fun _ : Fin 4 => AddCircle.haarAddCircle)) = _
  refine htransport_mul.trans ?_
  unfold cmp89Eq246NormalizedPhysicalFineToFineGreen
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  congr 1
  exact integral_congr_ae (by
    simpa [f, smul_eq_mul] using hae)

end

end YangMills.RG
