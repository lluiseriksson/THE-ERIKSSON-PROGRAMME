import YangMills.RG.BalabanCMP99Eq389CovariantLinkCommonMetric

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# CMP99 (3.89) first species at physical spacing

The sealed first-species consumer fixes spacing one.  This leaf keeps the two
inverse-spacing factors of the literal link correction and consumes one of
them through the already scaled `D^spacing G` component of Eq. (3.42).  The
remaining `spacing^-1` is visible in the conclusion.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {m q Nc : ℕ} [NeZero m] [NeZero q] [NeZero Nc]

/-- The physical-spacing link correction is the unit-spacing correction with
two explicit inverse-spacing factors. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_spacing_eq
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (h : FinBox 4 (m * (2 * q)) → ℝ)
    (phi : PhysicalGaugeZeroCochain 4 (m * (2 * q)) Nc)
    (x : FinBox 4 (m * (2 * q))) :
    ‖cmp99CovariantCutoffLinkDerivative rho U spacing h phi x‖ =
      spacing⁻¹ * spacing⁻¹ *
        ‖cmp99CovariantCutoffLinkDerivative rho U 1 h phi x‖ := by
  unfold cmp99CovariantCutoffLinkDerivative
  simp only [inv_one, one_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hspacing)]
  ring

/-- Direct first-species estimate at arbitrary positive physical spacing.

One inverse-spacing factor converts each unscaled covariant derivative into
the scaled derivative controlled by Eq. (3.42); the other remains outside the
finite four-direction sum. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_spacing_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (h : FinBox 4 (m * (2 * q)) → ℝ)
    (phi : PhysicalGaugeZeroCochain 4 (m * (2 * q)) Nc)
    (x : FinBox 4 (m * (2 * q))) (slope : ℝ)
    (hslope : 0 ≤ slope)
    (hforward : ∀ i : Fin 4, ‖h x - h (x.shift i)‖ ≤ slope)
    (hback : ∀ i : Fin 4, ‖h x - h (x.shiftBack i)‖ ≤ slope) :
    ‖cmp99CovariantCutoffLinkDerivative rho U spacing h phi x‖ ≤
      spacing⁻¹ * slope * ∑ i : Fin 4,
        (‖spacing⁻¹ • covariantD0CLM rho U phi
            ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ +
          ‖spacing⁻¹ • covariantD0CLM rho U phi
            ((FinBox.shiftBack x i, i) :
              PhysicalBond 4 (m * (2 * q)))‖) := by
  have hinv : 0 ≤ spacing⁻¹ := (inv_pos.mpr hspacing).le
  have hunit := norm_cmp99CovariantCutoffLinkDerivative_one_le
    rho U h phi x slope hforward hback
  rw [norm_cmp99CovariantCutoffLinkDerivative_spacing_eq
    rho U hspacing h phi x]
  calc
    spacing⁻¹ * spacing⁻¹ *
        ‖cmp99CovariantCutoffLinkDerivative rho U 1 h phi x‖ ≤
      spacing⁻¹ * spacing⁻¹ *
        (slope * ∑ i : Fin 4,
          (‖covariantD0CLM rho U phi
              ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ +
            ‖covariantD0CLM rho U phi
              ((FinBox.shiftBack x i, i) :
                PhysicalBond 4 (m * (2 * q)))‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hunit hinv) hinv
    _ = spacing⁻¹ * slope * ∑ i : Fin 4,
        (‖spacing⁻¹ • covariantD0CLM rho U phi
            ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ +
          ‖spacing⁻¹ • covariantD0CLM rho U phi
            ((FinBox.shiftBack x i, i) :
              PhysicalBond 4 (m * (2 * q)))‖) := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hspacing)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- The first regional-Green species at positive physical spacing, with one
common central owner metric. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_spacing_le
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing K c hc
      hKcoer B0 delta0 ell)
    (h : FinBox 4 (m * (2 * q)) → ℝ)
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc)
    (x : FinBox 4 (m * (2 * q))) (slope : ℝ) (hslope : 0 ≤ slope)
    (hforward : ∀ i : Fin 4, ‖h x - h (x.shift i)‖ ≤ slope)
    (hback : ∀ i : Fin 4, ‖h x - h (x.shiftBack i)‖ ≤ slope) :
    ‖cmp99CovariantCutoffLinkDerivative rho U spacing h
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega K hc hKcoer
            (singleFinitePiLp source v))) x‖ ≤
      spacing⁻¹ * slope * ∑ _i : Fin 4,
        ((B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ +
          (B0 * ell) *
              (Real.exp delta0 * Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ)))) * ‖v‖) := by
  let phi : PhysicalGaugeZeroCochain 4 (m * (2 * q)) Nc :=
    extendZeroZeroCLM Omega
      (cmp99RegionalDirichletGreen Omega K hc hKcoer
        (singleFinitePiLp source v))
  have hforwardD (i : Fin 4) :
      ‖spacing⁻¹ • covariantD0CLM rho U phi
          ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ ≤
        (B0 * ell) *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ := by
    have hD := C.left_derivative_bound.2.2 source
      ((x, i) : PhysicalBond 4 (m * (2 * q))) v
    simpa [phi, cmp99ActiveRegionSourceCovariantD0CLM] using hD
  have hbackD (i : Fin 4) :
      ‖spacing⁻¹ • covariantD0CLM rho U phi
          ((x.shiftBack i, i) : PhysicalBond 4 (m * (2 * q)))‖ ≤
        (B0 * ell) *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist m q (x.shiftBack i)
              source.1 : ℝ))) * ‖v‖ := by
    have hD := C.left_derivative_bound.2.2 source
      ((x.shiftBack i, i) : PhysicalBond 4 (m * (2 * q))) v
    simpa [phi, cmp99ActiveRegionSourceCovariantD0CLM] using hD
  refine (norm_cmp99CovariantCutoffLinkDerivative_spacing_le
    rho U hspacing h phi x slope hslope hforward hback).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_pos.mpr hspacing).le hslope)
  apply Finset.sum_le_sum
  intro i _hi
  apply add_le_add
  · exact hforwardD i
  · refine (hbackD i).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg C.B0_nonneg C.ell_pos.le)
    simpa [cmp99Eq342RescaledBlockDist] using
      (exp_neg_blockShift_dist_le_exp_mul (m := m) (n := 2 * q)
        x source.1 i C.delta0_pos.le)

end

end YangMills.RG
