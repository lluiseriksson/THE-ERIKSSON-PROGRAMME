import Mathlib

/-!
PRE-VALIDATION MINIMAL REPRODUCER: this file isolates the three generic
continuous-linear-map algebra steps used by `tmp/P2bEffectiveQuadratic.lean`.
It imports no project module and is executed before the project prerequisite
frontier in the Colab validation runner.
-/

open scoped RealInnerProductSpace

noncomputable section

noncomputable def reproGaugePrecision
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (bCount : ℝ) : H →L[ℝ] H :=
  D + bCount • (Q.adjoint.comp Q)

noncomputable def reproEffectiveQuadratic
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bWeighted bCount : ℝ) : F →L[ℝ] F :=
  bWeighted • ContinuousLinearMap.id ℝ F -
    (bWeighted * bCount) • (Q.comp (G.comp Q.adjoint))

theorem reproEffectiveQuadratic_isSymmetric
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bWeighted bCount : ℝ) (hG : G.IsSymmetric) :
    (reproEffectiveQuadratic Q G bWeighted bCount).IsSymmetric := by
  have hmiddle : ∀ x y,
      inner ℝ (Q (G (Q.adjoint x))) y =
        inner ℝ x (Q (G (Q.adjoint y))) := by
    intro x y
    calc
      inner ℝ (Q (G (Q.adjoint x))) y =
          inner ℝ (G (Q.adjoint x)) (Q.adjoint y) :=
        (ContinuousLinearMap.adjoint_inner_right Q _ _).symm
      _ = inner ℝ (Q.adjoint x) (G (Q.adjoint y)) := hG _ _
      _ = inner ℝ x (Q (G (Q.adjoint y))) :=
        ContinuousLinearMap.adjoint_inner_left Q _ _
  intro x y
  unfold reproEffectiveQuadratic
  change inner ℝ
      (bWeighted • x -
        (bWeighted * bCount) • Q (G (Q.adjoint x))) y =
    inner ℝ x
      (bWeighted • y -
        (bWeighted * bCount) • Q (G (Q.adjoint y)))
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, hmiddle]

noncomputable def reproSchurFineField
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bCount : ℝ) (eta : F) : H :=
  bCount • G (Q.adjoint eta)

theorem reproSchurFineField_euler
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bCount : ℝ)
    (hKG : (reproGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    D (reproSchurFineField Q G bCount eta) =
      bCount • Q.adjoint
        (eta - Q (reproSchurFineField Q G bCount eta)) := by
  have hpoint := congrArg
    (fun A : H →L[ℝ] H => A (Q.adjoint eta)) hKG
  change reproGaugePrecision D Q bCount (G (Q.adjoint eta)) =
    Q.adjoint eta at hpoint
  unfold reproSchurFineField
  simp only [map_smul, map_sub, smul_sub]
  simp only [reproGaugePrecision, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at hpoint
  apply eq_sub_iff_add_eq.mpr
  simpa only [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun x : H => bCount • x) hpoint

theorem repro_completedSquare
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    {bWeighted bCount : ℝ} (hbCount : bCount ≠ 0)
    (hKG : (reproGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    let phi := reproSchurFineField Q G bCount eta
    inner ℝ eta (reproEffectiveQuadratic Q G bWeighted bCount eta) =
      (bWeighted / bCount) * inner ℝ phi (D phi) +
        bWeighted * ‖eta - Q phi‖ ^ 2 := by
  dsimp only
  let phi := reproSchurFineField Q G bCount eta
  have hEuler := reproSchurFineField_euler D Q G bCount hKG eta
  have hEnergy :
      inner ℝ phi (D phi) =
        bCount * inner ℝ (Q phi) (eta - Q phi) := by
    rw [hEuler, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  simp only [reproEffectiveQuadratic, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right, inner_smul_right]
  change _ = (bWeighted / bCount) * inner ℝ phi (D phi) + _
  rw [hEnergy]
  have hQphi : Q phi = bCount • Q (G (Q.adjoint eta)) := by
    unfold phi reproSchurFineField
    rw [map_smul]
  rw [hQphi]
  simp only [inner_smul_left, conj_trivial]
  rw [← real_inner_self_eq_norm_sq, inner_sub_right, inner_sub_right]
  simp only [inner_sub_left, inner_smul_left, inner_smul_right, conj_trivial]
  field_simp [hbCount]
  rw [real_inner_comm eta (Q (G (Q.adjoint eta)))]
  ring

end
