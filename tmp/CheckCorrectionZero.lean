import YangMills.RG.BalabanCMP102PhysicalChartBudget

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

theorem orientedWilsonFactor_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (t : ℝ) :
    orientedWilsonFactor U 0 e t = orientedWilsonFactor U 0 e 0 := by
  have hcoord : (suLieCoordIso Nc).symm (0 : SUNLieCoord Nc) = 0 :=
    map_zero _
  have hmat : ((0 : SuLie Nc).toMatrix) = 0 := rfl
  have htz : t • (0 : Matrix (Fin Nc) (Fin Nc) ℂ) = 0 := smul_zero t
  have h0z : (0 : ℝ) • (0 : Matrix (Fin Nc) (Fin Nc) ℂ) = 0 :=
    zero_smul ℝ _
  cases h : e.sign
  · simp only [orientedWilsonFactor, orientedWilsonGenerator,
      flatOrientedSuMatrixTangent, h, Bool.false_eq_true, if_false,
      PiLp.zero_apply]
    rw [hcoord, hmat, neg_zero, htz, h0z]
  · simp only [orientedWilsonFactor, orientedWilsonGenerator,
      flatOrientedSuMatrixTangent, h, if_true, PiLp.zero_apply]
    rw [hcoord, hmat, htz, h0z]

theorem cmp98ContourMatrixCurve_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U 0 es t =
      cmp98ContourMatrixCurve U 0 es 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [cmp98ContourMatrixCurve]
      rw [orientedWilsonFactor_zero_field U e t, ih]

theorem cmp98Eq119NonlinearBlockCurve_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearBlockCurve U 0 b t =
      cmp98Eq119NonlinearBlockCurve U 0 b 0 := by
  unfold cmp98Eq119NonlinearBlockCurve
  have hsu :
      physicalCochainToSuMatrixTangent
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) = 0 := by
    funext e
    simp [physicalCochainToSuMatrixTangent]
  rw [hsu]
  have hamb :
      physicalSuTangentToAmbient
          (0 : PhysicalSuMatrixTangent d (M * N') Nc) = 0 := by
    funext e i j
    rfl
  rw [hamb]
  have htz :
      t • (0 : PhysicalAmbientMatrixTangent d (M * N') Nc) = 0 :=
    smul_zero t
  have h0z :
      (0 : ℝ) • (0 : PhysicalAmbientMatrixTangent d (M * N') Nc) = 0 :=
    zero_smul ℝ _
  rw [htz, h0z]
  rw [cmp98ContourMatrixCurve_zero_field U
    (cmp98SourceCoarseBondPath (Nc := Nc) b) t]

theorem deriv_cmp98Eq119NonlinearBlockCurve_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') :
    deriv (cmp98Eq119NonlinearBlockCurve U 0 b) 0 = 0 := by
  have hfun :
      cmp98Eq119NonlinearBlockCurve U 0 b =
        fun _ => cmp98Eq119NonlinearBlockCurve U 0 b 0 := by
    funext t
    exact cmp98Eq119NonlinearBlockCurve_zero_field U b t
  rw [hfun]
  exact
    (hasDerivAt_const (x := (0 : ℝ))
      (c := cmp98Eq119NonlinearBlockCurve U 0 b 0)).deriv

theorem cmp98Eq119NonlinearRightVariation_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearRightVariation U 0 b = 0 := by
  unfold cmp98Eq119NonlinearRightVariation
  have hderiv :
      deriv (cmp98Eq119NonlinearBlockCurve U
        (0 : PhysicalGaugeOneCochain d (M * N') Nc) b) 0 = 0 :=
    deriv_cmp98Eq119NonlinearBlockCurve_zero_field U b
  rw [hderiv, zero_mul]

theorem cmp98Eq119NonlinearRelativeDeviation_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq119NonlinearRelativeDeviation U 0 b t = 0 := by
  unfold cmp98Eq119NonlinearRelativeDeviation
  rw [cmp98Eq119NonlinearBlockCurve_zero_field U b t,
    cmp98Eq119NonlinearBlockCurve_zero_mul_inverseAtZero]
  exact sub_self 1

theorem cmp98Eq122NonlinearLogRemainder_zero_field
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq122NonlinearLogRemainder U 0 b t = 0 := by
  unfold cmp98Eq122NonlinearLogRemainder
  rw [show cmp98Eq119NonlinearLogCoordinate U 0 b t = 0 by
    rw [show cmp98Eq119NonlinearLogCoordinate U 0 b t =
        cmp98Eq119NonlinearLogCoordinate U 0 b 0 by
      unfold cmp98Eq119NonlinearLogCoordinate
      rw [cmp98Eq119NonlinearRelativeDeviation_zero_field U b t,
        cmp98Eq119NonlinearRelativeDeviation_zero]]
    exact cmp98Eq119NonlinearLogCoordinate_zero U 0 b,
    cmp98Eq119NonlinearRightVariation_zero_field U b]
  exact sub_eq_zero.mpr (smul_zero t).symm

example
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U 0) :
    cmp102PhysicalNonlinearCorrectionOfBudget U 0 B = 0 := by
  apply PiLp.ext
  intro b
  have hambient :
      cmp98LieCoordToAmbientCLM Nc
          (cmp102PhysicalNonlinearCorrectionOfBudget U 0 B b) = 0 := by
    rw [cmp102PhysicalNonlinearCorrectionOfBudget_toMatrix]
    exact cmp98Eq122NonlinearLogRemainder_zero_field U b 1
  calc
    cmp102PhysicalNonlinearCorrectionOfBudget U 0 B b =
        cmp98AmbientToLieCoordCLM Nc
          (cmp98LieCoordToAmbientCLM Nc
            (cmp102PhysicalNonlinearCorrectionOfBudget U 0 B b)) := by
      symm
      exact cmp98AmbientToLieCoordCLM_leftInverse _
    _ = 0 := by rw [hambient, map_zero]

end

end YangMills.RG
