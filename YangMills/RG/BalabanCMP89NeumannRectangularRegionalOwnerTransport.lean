import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalRegionalBound

/-!
# CMP89 regional Green: fixed-rate owner transport

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

This module transports the physical CMP89 (2.42) regional value estimate to
one fixed owner rate.  The period floor and metric bridge remain explicit;
it does not manufacture an owner map or a physical rectangle dictionary.
-/

namespace YangMills.RG

noncomputable section

/-- A coordinatewise reflection-period floor removes the varying geometric
denominators without a rectangle-cardinality factor. -/
theorem cmp89NeumannReflectionPeriodProduct_uniform_le_draft
    {m : Fin 4 → ℤ} {ell : ℕ} (hell : 0 < ell)
    {rho : ℝ} (hrho : 0 < rho)
    (hperiod : ∀ mu, ell ≤ cmp89NeumannReflectionPeriodNat m mu) :
    (∏ mu,
        2 / (1 - Real.exp
          (-(rho / (ell : ℝ)) *
            (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) ≤
      (2 / (1 - Real.exp (-rho))) ^ 4 := by
  have hellReal : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hdenPos : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hcoord : ∀ mu,
      2 / (1 - Real.exp
          (-(rho / (ell : ℝ)) *
            (cmp89NeumannReflectionPeriodNat m mu : ℝ))) ≤
        2 / (1 - Real.exp (-rho)) := by
    intro mu
    have hperiodReal :
        (ell : ℝ) ≤ (cmp89NeumannReflectionPeriodNat m mu : ℝ) := by
      exact_mod_cast hperiod mu
    have hscale : (rho / (ell : ℝ)) * (ell : ℝ) = rho := by
      field_simp [ne_of_gt hellReal]
    have hmul := mul_le_mul_of_nonneg_left hperiodReal
      (div_nonneg hrho.le hellReal.le)
    have hexp :
        Real.exp (-(rho / (ell : ℝ)) *
            (cmp89NeumannReflectionPeriodNat m mu : ℝ)) ≤
          Real.exp (-rho) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul]
      nlinarith
    have hden :
        1 - Real.exp (-rho) ≤
          1 - Real.exp
            (-(rho / (ell : ℝ)) *
              (cmp89NeumannReflectionPeriodNat m mu : ℝ)) := by
      linarith
    exact div_le_div_of_nonneg_left (by norm_num) hdenPos hden
  calc
    (∏ mu,
        2 / (1 - Real.exp
          (-(rho / (ell : ℝ)) *
            (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) ≤
        ∏ _mu : Fin 4, (2 / (1 - Real.exp (-rho))) := by
      apply Finset.prod_le_prod
      · intro mu _
        have hP : 0 <
            (cmp89NeumannReflectionPeriodNat m mu : ℝ) := by
          exact_mod_cast lt_of_lt_of_le hell (hperiod mu)
        have hdelta : 0 < rho / (ell : ℝ) :=
          div_pos hrho hellReal
        have hden : 0 ≤
            1 - Real.exp
              (-(rho / (ell : ℝ)) *
                (cmp89NeumannReflectionPeriodNat m mu : ℝ)) := by
          rw [sub_nonneg]
          exact Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hdelta.le) hP.le)
        exact div_nonneg (by norm_num) hden
      · intro mu _
        exact hcoord mu
    _ = (2 / (1 - Real.exp (-rho))) ^ 4 := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The fine signed-`l1` decay gives one fixed owner rate once the exact
fine-to-owner metric bridge is supplied. -/
theorem cmp89NeumannFineWeight_le_ownerWeight_of_metric_bridge_draft
    {ell : ℕ} (hell : 0 < ell) {rho : ℝ} (hrho : 0 ≤ rho)
    (u : Fin 4 → ℤ) (ownerDist boundary : ℝ)
    (hmetric : (ell : ℝ) * ownerDist ≤
      cmp89Eq251LatticeL1Length u + boundary) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (ell : ℝ)) u ≤
      Real.exp ((rho / (ell : ℝ)) * boundary) *
        Real.exp (-rho * ownerDist) := by
  have hellReal : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hrate : 0 ≤ rho / (ell : ℝ) := div_nonneg hrho hellReal.le
  have hscale : (rho / (ell : ℝ)) * (ell : ℝ) = rho := by
    field_simp [ne_of_gt hellReal]
  have hmul := mul_le_mul_of_nonneg_left hmetric hrate
  have hmetricScaled :
      rho * ownerDist ≤
        (rho / (ell : ℝ)) * cmp89Eq251LatticeL1Length u +
          (rho / (ell : ℝ)) * boundary := by
    calc
      rho * ownerDist =
          (rho / (ell : ℝ)) * ((ell : ℝ) * ownerDist) := by
        rw [← mul_assoc, hscale]
      _ ≤ (rho / (ell : ℝ)) *
          (cmp89Eq251LatticeL1Length u + boundary) := hmul
      _ = (rho / (ell : ℝ)) * cmp89Eq251LatticeL1Length u +
          (rho / (ell : ℝ)) * boundary := by ring
  have hexponent :
      -(rho / (ell : ℝ) * cmp89Eq251LatticeL1Length u) ≤
        (rho / (ell : ℝ)) * boundary - rho * ownerDist := by
    linarith
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  calc
    Real.exp
        (-(rho / (ell : ℝ)) * ∑ mu, ((u mu).natAbs : ℝ)) ≤
      Real.exp
        ((rho / (ell : ℝ)) * boundary - rho * ownerDist) :=
      by
        simpa [cmp89Eq251LatticeL1Length] using
          (Real.exp_le_exp.mpr hexponent)
    _ = Real.exp ((rho / (ell : ℝ)) * boundary) *
        Real.exp (-rho * ownerDist) := by
      rw [sub_eq_add_neg, Real.exp_add]
      rw [neg_mul]

/-- The regional CMP89 (2.42) value estimate at fine rate `rho / L^j`
transports to one fixed owner rate `rho` once the two source-facing geometric
facts are supplied.  No owner map is accepted or constructed here. -/
theorem norm_cmp89Eq248PhysicalRegionalGreen_le_owner_of_geometry_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m : Fin 4 → ℤ}
    {regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → ℂ}
    (R : CMP89NeumannReflectionRepresentationCertificate m regionalGreen
      (cmp89Eq248PhysicalFullLatticeGreen L j mass a))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m)
    (ownerDist boundary : ℝ)
    (hperiod : ∀ mu, L ^ j ≤ cmp89NeumannReflectionPeriodNat m mu)
    (hmetric : ((L ^ j : ℕ) : ℝ) * ownerDist ≤
      cmp89Eq251LatticeL1Length (x.1 - n.1) + boundary) :
    ‖regionalGreen x n‖ ≤
      (2 : ℝ) ^ 4 *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((2 / (1 - Real.exp (-rho))) ^ 4 *
          (Real.exp ((rho / ((L ^ j : ℕ) : ℝ)) * boundary) *
            Real.exp (-rho * ownerDist))) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hell : 0 < L ^ j := pow_pos hL j
  have hbase :=
    norm_cmp89Eq248PhysicalRegionalGreen_le_of_representation_draft
      ha hrho hamplitude hradius hwindow hmass R x n
  have hperiodBound :=
    cmp89NeumannReflectionPeriodProduct_uniform_le_draft
      hell hrho hperiod
  have hweightBound :=
    cmp89NeumannFineWeight_le_ownerWeight_of_metric_bridge_draft
      hell hrho.le (x.1 - n.1) ownerDist boundary hmetric
  have hB0 : 0 ≤
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho :=
    (cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
      (L := L) (j := j)
      ha hrho hamplitude hradius hwindow hmass).B0_nonneg
  have hA : 0 ≤ (2 : ℝ) ^ 4 *
      cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho :=
    mul_nonneg (by positivity) hB0
  have hweight : 0 ≤
      cmp89SignedLatticeL1ExponentialWeight
        (rho / ((L ^ j : ℕ) : ℝ)) (x.1 - n.1) := by
    rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
    positivity
  have hden : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hconstant : 0 ≤ (2 / (1 - Real.exp (-rho))) ^ 4 := by
    exact pow_nonneg (div_nonneg (by norm_num) hden.le) _
  calc
    ‖regionalGreen x n‖ ≤
        (2 : ℝ) ^ 4 *
          cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
          ((∏ mu,
              2 / (1 - Real.exp
                (-(rho / ((L ^ j : ℕ) : ℝ)) *
                  (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
            cmp89SignedLatticeL1ExponentialWeight
              (rho / ((L ^ j : ℕ) : ℝ)) (x.1 - n.1)) := hbase
    _ ≤ (2 : ℝ) ^ 4 *
          cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
          ((2 / (1 - Real.exp (-rho))) ^ 4 *
            cmp89SignedLatticeL1ExponentialWeight
              (rho / ((L ^ j : ℕ) : ℝ)) (x.1 - n.1)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hperiodBound hweight) hA
    _ ≤ (2 : ℝ) ^ 4 *
          cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
          ((2 / (1 - Real.exp (-rho))) ^ 4 *
            (Real.exp ((rho / ((L ^ j : ℕ) : ℝ)) * boundary) *
              Real.exp (-rho * ownerDist))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweightBound hconstant) hA

end

end YangMills.RG
