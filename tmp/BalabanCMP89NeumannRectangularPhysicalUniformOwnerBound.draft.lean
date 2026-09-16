import YangMills.RG.BalabanCMP89NeumannRectangularPeriodFloor
import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalOwnerGeometry

/-!
# CMP89 rectangular regional Green: physical fixed owner rate

Draft only.  This source has not been promoted or compiler-verified.

The physical half-open rectangle, its reflection periods and the canonical
CMP99 localization owners are constructed by the preceding dictionaries.
The exact boundary `2*(L^(depth+1)-1)` is paid visibly by `exp (2*rho)`;
there is no depth-dependent replacement constant.
-/

namespace YangMills.RG

noncomputable section

/-- The physical CMP89 regional value bound at fine rate
`rho/L^(depth+1)` becomes one owner-rate `rho` estimate with a depth-free
amplitude.  CMP89 (2.42) remains the named analytic representation input. -/
theorem norm_cmp89Eq248PhysicalRegionalGreen_le_physicalOwner_uniform_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hside : ∀ mu, ((L ^ (depth + 1) : ℕ) : ℤ) ≤ m mu)
    (hfit : ∀ mu, m mu ≤
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) : ℕ))
    {regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → ℂ}
    (R : CMP89NeumannReflectionRepresentationCertificate m regionalGreen
      (cmp89Eq248PhysicalFullLatticeGreen L (depth + 1) mass a))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    ‖regionalGreen x n‖ ≤
      (2 : ℝ) ^ 4 *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp (2 * rho) *
            Real.exp (-rho *
              (finBoxDist
                (cmp99Eq389SourceLocalizationOwner L K Q depth
                  (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x))
                (cmp99Eq389SourceLocalizationOwner L K Q depth
                  (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)) : ℝ)))) := by
  let ell : ℕ := L ^ (depth + 1)
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hell : 0 < ell := by
    exact pow_pos hL (depth + 1)
  have hellReal : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hperiod : ∀ mu, ell ≤ cmp89NeumannReflectionPeriodNat m mu := by
    intro mu
    exact cmp89NeumannReflectionPeriodNat_ge_scale_of_side_floor_draft
      hm hside mu
  have hmetric :=
    cmp89RectanglePhysicalOwner_mul_dist_le_l1_add_boundary_draft
      depth hfit x n
  have hbase :=
    norm_cmp89Eq248PhysicalRegionalGreen_le_owner_of_geometry_draft
      (L := L) (j := depth + 1)
      ha hrho hamplitude hradius hwindow hmass R x n
      (finBoxDist
        (cmp99Eq389SourceLocalizationOwner L K Q depth
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x))
        (cmp99Eq389SourceLocalizationOwner L K Q depth
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)) : ℝ)
      (2 * (L ^ (depth + 1) - 1) : ℕ)
      hperiod (by simpa [Nat.cast_pow] using hmetric)
  have hboundaryNat : 2 * (ell - 1) ≤ 2 * ell := by omega
  have hboundaryReal :
      ((2 * (ell - 1) : ℕ) : ℝ) ≤ 2 * (ell : ℝ) := by
    exact_mod_cast hboundaryNat
  have hrate : 0 ≤ rho / (ell : ℝ) :=
    div_nonneg hrho.le hellReal.le
  have hboundaryScaled :
      (rho / (ell : ℝ)) * ((2 * (ell - 1) : ℕ) : ℝ) ≤ 2 * rho := by
    calc
      (rho / (ell : ℝ)) * ((2 * (ell - 1) : ℕ) : ℝ) ≤
          (rho / (ell : ℝ)) * (2 * (ell : ℝ)) :=
        mul_le_mul_of_nonneg_left hboundaryReal hrate
      _ = 2 * rho := by field_simp [ne_of_gt hellReal]
  have hboundaryExp :
      Real.exp ((rho / (ell : ℝ)) * ((2 * (ell - 1) : ℕ) : ℝ)) ≤
        Real.exp (2 * rho) :=
    Real.exp_le_exp.mpr hboundaryScaled
  have hB0 : 0 ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho :=
    (cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
      (L := L) (j := depth + 1)
      ha hrho hamplitude hradius hwindow hmass).B0_nonneg
  have hA : 0 ≤ (2 : ℝ) ^ 4 *
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho :=
    mul_nonneg (by positivity) hB0
  have hden : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hconstant : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 :=
    pow_nonneg (div_nonneg (by norm_num) hden.le) _
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hboundaryExp (Real.exp_pos _).le)
      hconstant)
    hA)

end

end YangMills.RG
