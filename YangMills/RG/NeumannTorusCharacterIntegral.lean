import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
PRE-VALIDATION: production source present; .olean not materialized and
production compiler result not verified. The exact draft passed HOT ledger1227.
This is normalized Haar character orthogonality, not a physical source equation.
The physical volume convention is linked explicitly at period one.
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
