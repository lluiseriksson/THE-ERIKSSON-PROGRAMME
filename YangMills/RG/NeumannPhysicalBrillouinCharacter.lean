import YangMills.RG.NeumannTorusCharacterIntegral
import YangMills.RG.BalabanCMP89NormalizedBrillouinToTorusMeasure

/-!
Cold compiler-verified at source29a48ac4bb1058cd71b74f65029e918d49e74b60,
2026-09-07, ledger1231; output and exact audits independently preserved.
Proof body unchanged from that cold source and HOT ledger1230.
Consume the literal translated physical Brillouin parameter
and its already normalized measure. No second Jacobian, no free phase map.
This integer-character identity is not the full alias-weighted source
equation, finite operator action, regional inverse or window15.
-/

open MeasureTheory

namespace YangMills.RG
noncomputable section

theorem neumannTorus_volumeCharacterIntegral (u : Fin 4 → ℤ) :
    (∫ t : UnitAddTorus (Fin 4), UnitAddTorus.mFourier u t
      ∂(volume : Measure (UnitAddTorus (Fin 4)))) =
      if u = 0 then (1 : ℂ) else 0 := by
  simpa only [MeasureTheory.volume_pi,
    neumannUnitCircle_volume_eq_normalizedHaar] using
    neumannTorus_normalizedCharacterIntegral u

theorem neumannPhysicalBrillouin_character_phase
    (u : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    UnitAddTorus.mFourier (-u) (cmp89PhysicalBrillouinToUnitAddTorus x) =
      Complex.exp (Complex.I *
        (∑ mu, (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ) *
          (u mu : ℂ))) := by
  have h := cmp89UnitAddTorus_mFourier_neg_eq_exp_physicalPhase u
    (fun mu => (1 / 2 : ℝ) - (2 * Real.pi)⁻¹ * x mu)
  rw [cmp89Eq248NegativeTwoPiTorusMomentum_physicalBrillouin] at h
  simpa only [cmp89PhysicalBrillouinToUnitAddTorus,
    cmp89PhysicalBrillouinToUnitAddCircle] using h

theorem neumannPhysicalBrillouin_integerCharacterIntegral
    (u : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      (fun x => Complex.exp (Complex.I *
        (∑ mu, (cmp89Eq251PhysicalBrillouinParameter x mu : ℂ) *
          (u mu : ℂ)))) =
      if u = 0 then (1 : ℂ) else 0 := by
  calc
    _ = cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => UnitAddTorus.mFourier (-u)
          (cmp89PhysicalBrillouinToUnitAddTorus x)) := by
      congr 1
      funext x
      exact (neumannPhysicalBrillouin_character_phase u x).symm
    _ = ∫ t : UnitAddTorus (Fin 4), UnitAddTorus.mFourier (-u) t
        ∂(volume : Measure (UnitAddTorus (Fin 4))) :=
      (integral_unitAddTorus_eq_cmp89NormalizedBrillouin
        (UnitAddTorus.mFourier (-u))).symm
    _ = _ := by
      simpa only [neg_eq_zero] using neumannTorus_volumeCharacterIntegral (-u)

end
end YangMills.RG
