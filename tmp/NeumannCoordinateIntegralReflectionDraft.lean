import YangMills.RG.IntervalIntegralPiCoordinateTransport

/-!
# PRE-VALIDATION: coordinate reflection of an interval product integral
Source present; .olean not materialized; result not compiler-verified.
This measure-theoretic leaf takes both integrability proofs explicitly.
The physical consumer must produce them from its common-strip conditions.
The half-open interval is handled by interval integration, not a false
pointwise invariance of uIoc under reflection. No Green law is assumed.
-/

namespace YangMills.RG
open MeasureTheory
noncomputable section

def neumannIntervalCoordinateReflection {n : ℕ} (i : Fin n) (b : ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if k = i then b - x k else x k

theorem neumannIntervalCoordinateReflection_insertNth
    {n : ℕ} (i : Fin (n + 1)) (b x : ℝ) (y : Fin n → ℝ) :
    neumannIntervalCoordinateReflection i b (i.insertNth x y) =
      i.insertNth (b - x) y := by
  funext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · simp [neumannIntervalCoordinateReflection]
  · simp [neumannIntervalCoordinateReflection, Fin.succAbove_ne]

theorem neumannIntegral_coordinateReflection
    {n : ℕ} (i : Fin (n + 1)) {b : ℝ} (hb : 0 ≤ b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (Fin (n + 1) → ℝ) → E)
    (hf : Integrable f
      (Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc 0 b)))
    (hr : Integrable (fun x => f (neumannIntervalCoordinateReflection i b x))
      (Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc 0 b))) :
    (∫ x, f (neumannIntervalCoordinateReflection i b x)
      ∂(Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc 0 b))) =
    ∫ x, f x
      ∂(Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc 0 b)) := by
  apply integral_pi_restrict_uIoc_eq_of_coordinate_intervalIntegral_ae_eq hb i hr hf
  apply Filter.Eventually.of_forall
  intro y
  simp_rw [neumannIntervalCoordinateReflection_insertNth]
  simpa using (intervalIntegral.integral_comp_sub_left
    (a := 0) (b := b) (fun x => f (i.insertNth x y)) b)

#print axioms neumannIntervalCoordinateReflection_insertNth
#print axioms neumannIntegral_coordinateReflection

end
end YangMills.RG
