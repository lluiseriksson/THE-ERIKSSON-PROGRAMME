import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Mathlib-only normalization repro, not a physical source equation.
The Fourier library uses normalized Haar while the physical measure bridge
uses volume. At period one they agree by an explicit measure equality.
-/

open MeasureTheory

namespace YangMills.RG
noncomputable section

theorem neumannUnitCircle_volume_eq_normalizedHaar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

theorem neumannTorus_normalizedCharacterIntegral (u : Fin 4 → ℤ) :
    (∫ t : UnitAddTorus (Fin 4), UnitAddTorus.mFourier u t
      ∂Measure.pi (fun _ : Fin 4 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) =
      if u = 0 then (1 : ℂ) else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 4))) (0 : Fin 4 → ℤ) u
  simpa [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, eq_comm] using h

end
end YangMills.RG

#print axioms YangMills.RG.neumannUnitCircle_volume_eq_normalizedHaar
#print axioms YangMills.RG.neumannTorus_normalizedCharacterIntegral
