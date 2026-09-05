import YangMills.RG.BalabanCMP89SourceNeumannRestrictedParallelDefectBound
import YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling
import YangMills.RG.BalabanCMP89SourceNeumannTwoScalePoincareAdapter
import YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateMonotonicity
import YangMills.RG.BalabanCMP99SourcePoincarePositiveRadiusReachability

/-!
# Literal physical CMP89 Neumann derivative feedback

This module combines the two source-printed derivative species without a
boundary or carrier-cardinality term, then cancels the fine/coarse
lattice-spacing conventions exactly.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal coefficient multiplying the normalized fine derivative after
the path-length, path-layer and lattice-spacing factors cancel. -/
noncomputable def cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient
    (d M : ℕ) : ℝ :=
  2 * cmp99SourceBlockAverageWeight M d

/-- The literal coefficient multiplying the fine field in the physical
two-species derivative bound.  It keeps the source block-average mass outside
the already named one-step `Ubar` coefficient. -/
noncomputable def cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
    (d M : ℕ) (etaFine etaCoarse : ℝ) : ℝ :=
  2 * cmp99SourceBlockAverageWeight M d *
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient
      d M etaFine etaCoarse

theorem cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient_nonneg
    (d M : ℕ) :
    0 ≤ cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M := by
  unfold cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient
    cmp99SourceBlockAverageWeight
  positivity

theorem cmp89SourceNeumannPhysicalFieldFeedbackCoefficient_nonneg
    (d M : ℕ) (etaFine etaCoarse : ℝ) :
    0 ≤ cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
      d M etaFine etaCoarse := by
  unfold cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient
    cmp99SourceBlockAverageWeight
  positivity

/-- Exact scalar value of the two-scale feedback gate at the source dimension
and block ratio, using the deliberately smaller common target `4⁻¹⁰`.  This
is a compatibility value, not an assertion that a physical background
attains either deviation radius. -/
theorem cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_d4_M4_q10_eq :
    cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp99OneScaleBlockPoincareConstant 4 4 *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 10) (((4 : ℝ)⁻¹) ^ 10) =
      (729 : ℝ) / 2048 := by
  norm_num [cmp99OneScaleBlockPoincareConstant,
    cmp89SourceNeumannPhysicalFieldFeedbackCoefficient,
    cmp89SourceNeumannPhysicalOneStepDefectCoefficient,
    cmp99SourceBlockAverageWeight, max_eq_left]

/-- The same positive target satisfies the literal two-scale feedback window
whenever the next lattice spacing is at most one.  The two spacing-dependent
Poincare constants are reduced explicitly; no operator-attainment claim is
hidden in this scalar lemma. -/
theorem cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_d4_M4_q10_lt_one
  {spacing : ℝ} (hnext : |(4 : ℝ) * spacing| ≤ 1) :
    cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing *
        cmp89SourceNeumannOneScalePoincareConstant 4 4
          ((4 : ℝ) * spacing) *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 10) (((4 : ℝ)⁻¹) ^ 10) < 1 := by
  have hcoarseSq : ((4 : ℝ) * spacing) ^ 2 ≤ 1 := by
    nlinarith [sq_abs ((4 : ℝ) * spacing),
      abs_nonneg ((4 : ℝ) * spacing)]
  have hfineAbs : |spacing| ≤ 1 := by
    have hscaled : |(4 : ℝ) * spacing| = 4 * |spacing| := by
      rw [abs_mul]
      norm_num
    rw [hscaled] at hnext
    nlinarith [abs_nonneg spacing]
  have hfineSq : spacing ^ 2 ≤ 1 := by
    nlinarith [sq_abs spacing, abs_nonneg spacing]
  simp only [cmp89SourceNeumannOneScalePoincareConstant,
    max_eq_right hfineSq, max_eq_right hcoarseSq, mul_one]
  rw [cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_d4_M4_q10_eq]
  norm_num

/-- Monotonicity of the literal field-feedback coefficient in both
nonnegative source deviation radii. -/
theorem cmp89SourceNeumannPhysicalFieldFeedbackCoefficient_mono
    {etaFine etaCoarse etaFine' etaCoarse' : ℝ}
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (hfine : etaFine ≤ etaFine')
    (hcoarse : etaCoarse ≤ etaCoarse') :
    cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
        d M etaFine etaCoarse ≤
      cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
        d M etaFine' etaCoarse' := by
  unfold cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
  apply mul_le_mul_of_nonneg_left
    (cmp89SourceNeumannPhysicalOneStepDefectCoefficient_mono
      etaFine_nonneg etaCoarse_nonneg hfine hcoarse)
  unfold cmp99SourceBlockAverageWeight
  positivity

/-- Every nonnegative pair below the common `4⁻¹⁰` target satisfies the
literal two-scale feedback gate at the source dimension and block ratio. -/
theorem cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_lt_one_of_le_d4_M4_q10
    {spacing etaFine etaCoarse : ℝ}
    (hnext : |(4 : ℝ) * spacing| ≤ 1)
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (hfine : etaFine ≤ ((4 : ℝ)⁻¹) ^ 10)
    (hcoarse : etaCoarse ≤ ((4 : ℝ)⁻¹) ^ 10) :
    cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing *
        cmp89SourceNeumannOneScalePoincareConstant 4 4
          ((4 : ℝ) * spacing) *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
          4 4 etaFine etaCoarse < 1 := by
  calc
    _ ≤ cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing *
        cmp89SourceNeumannOneScalePoincareConstant 4 4
          ((4 : ℝ) * spacing) *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
          (((4 : ℝ)⁻¹) ^ 10) (((4 : ℝ)⁻¹) ^ 10) := by
      apply mul_le_mul_of_nonneg_left
        (cmp89SourceNeumannPhysicalFieldFeedbackCoefficient_mono
          etaFine_nonneg etaCoarse_nonneg hfine hcoarse)
      exact mul_nonneg
        (cmp89SourceNeumannOneScalePoincareConstant_pos spacing).le
        (cmp89SourceNeumannOneScalePoincareConstant_pos
          ((4 : ℝ) * spacing)).le
    _ < 1 :=
      cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_d4_M4_q10_lt_one hnext

/-- Literal radius form of the reached two-scale feedback gate. -/
theorem cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_lt_one_of_radius_bounds_d4_M4
    {spacing epsilon nextRadius : ℝ}
    (hspacing : 0 < spacing)
    (hnextSpacing : |(4 : ℝ) * spacing| ≤ 1)
    (epsilon_nonneg : 0 ≤ epsilon)
    (nextRadius_nonneg : 0 ≤ nextRadius)
    (hfine : epsilon ≤ spacing * (((4 : ℝ)⁻¹) ^ 10))
    (hcoarse : nextRadius ≤
      ((4 : ℝ) * spacing) * (((4 : ℝ)⁻¹) ^ 10)) :
    cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing *
        cmp89SourceNeumannOneScalePoincareConstant 4 4
          ((4 : ℝ) * spacing) *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
          (epsilon / spacing)
          (nextRadius / ((4 : ℝ) * spacing)) < 1 := by
  have hcoarseSpacing : 0 < (4 : ℝ) * spacing :=
    mul_pos (by norm_num) hspacing
  apply cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_lt_one_of_le_d4_M4_q10
    hnextSpacing
  · exact div_nonneg epsilon_nonneg hspacing.le
  · exact div_nonneg nextRadius_nonneg hcoarseSpacing.le
  · exact (div_le_iff₀ hspacing).2 (by simpa [mul_comm] using hfine)
  · exact (div_le_iff₀ hcoarseSpacing).2
      (by simpa [mul_comm] using hcoarse)

/-- At each fixed positive physical spacing in the next-scale window, the
literal two-step `Ubar` source flow reaches the stronger quantitative
feedback gate at one positive source radius.  This is still a depth-two
reachability statement, not an arbitrary-depth CMP89 (2.42) theorem. -/
theorem exists_pos_cmp89SourceNeumann_twoScale_physical_feedback_radius
    {Nc : ℕ} [NeZero Nc]
    (spacing : ℝ) (hspacing : 0 < spacing)
    (hnextSpacing : |(4 : ℝ) * spacing| ≤ 1) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      CMP99SourceUbarClosedBudget 4 4 Nc 2 epsilon ∧
      cmp89SourceNeumannOneScalePoincareConstant 4 4 spacing *
          cmp89SourceNeumannOneScalePoincareConstant 4 4
            ((4 : ℝ) * spacing) *
          cmp89SourceNeumannPhysicalFieldFeedbackCoefficient 4 4
            (epsilon / spacing)
            (cmp99SourceUbarNextFineRadius 4 4 epsilon /
              ((4 : ℝ) * spacing)) < 1 := by
  let q : ℝ := ((4 : ℝ)⁻¹) ^ 10
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  obtain ⟨radius, hradius, hrange⟩ :=
    exists_pos_poincare_admissibleRadius
      (d := 4) (M := 4) (Nc := Nc) 2 spacing
  have htarget : 0 < (4 : ℝ) * spacing * q := by positivity
  have hnextEvent :
      {epsilon : ℝ |
        cmp99SourceUbarNextFineRadius 4 4 epsilon <
          (4 : ℝ) * spacing * q} ∈ 𝓝 0 := by
    have hcont :=
      continuousAt_cmp99SourceUbarNextFineRadius_zero
        (d := 4) (M := 4)
    have h := hcont.eventually_lt_const (by
      simpa only [cmp99SourceUbarNextFineRadius_zero] using htarget)
    simpa only [cmp99SourceUbarNextFineRadius_zero] using h
  obtain ⟨rNext, hrNext, hNextBall⟩ := Metric.mem_nhds_iff.mp hnextEvent
  let epsilon : ℝ := min radius (min rNext (spacing * q)) / 2
  have hmin_pos : 0 < min radius (min rNext (spacing * q)) :=
    lt_min hradius (lt_min hrNext (mul_pos hspacing hq))
  have hhalf_lt :
      min radius (min rNext (spacing * q)) / 2 <
        min radius (min rNext (spacing * q)) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hmin_pos]
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos hmin_pos (by norm_num)
  have hepsilon_radius : epsilon < radius := by
    dsimp only [epsilon]
    exact hhalf_lt.trans_le (min_le_left _ _)
  have hepsilon_next : epsilon < rNext := by
    dsimp only [epsilon]
    exact hhalf_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilon_fine : epsilon ≤ spacing * q := by
    dsimp only [epsilon]
    exact hhalf_lt.le.trans
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hbudget, _hPoincare⟩ :=
    hrange hepsilon.le hepsilon_radius
  have hepsilon_mem : epsilon ∈ Metric.ball (0 : ℝ) rNext := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg hepsilon.le]
    exact hepsilon_next
  have hnext : cmp99SourceUbarNextFineRadius 4 4 epsilon ≤
      ((4 : ℝ) * spacing) * q :=
    (hNextBall hepsilon_mem).le
  refine ⟨epsilon, hepsilon, hbudget, ?_⟩
  exact cmp89SourceNeumannPhysicalTwoScaleFeedbackGate_lt_one_of_radius_bounds_d4_M4
    hspacing hnextSpacing hepsilon.le
      (hbudget.toScalarBudget.radiusAt_nonneg (k := 1) (by norm_num))
      hepsilon_fine hnext

/-- Before physical scaling is substituted, the normalized coarse derivative
is bounded by the restricted straight defect plus the restricted `Ubar`
remainder.  The former sees raw Neumann energy only; the latter sees the field
norm only. -/
theorem norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le_raw_feedback
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    let psi := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) phi
    ‖cmp89SourceNeumannRegionalCovariantD0CLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (matrixSUNAdjointModel Nc) V ((M : ℝ) * spacing) psi‖ ^ 2 ≤
      ‖(((M : ℝ) * spacing)⁻¹)‖ ^ 2 *
          (2 * cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
            ‖cmp89SourceNeumannRegionalRawD0 Omega
              (matrixSUNAdjointModel Nc) U phi‖ ^ 2) +
        2 * cmp99SourceBlockAverageWeight M d *
          cmp89SourceNeumannOneStepDefectCoefficient
            (d := d) (M := M) spacing epsilonFine epsilonCoarse *
          ‖phi‖ ^ 2 := by
  let OmegaC := cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
  let D := restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
    (cmp99SourceParallelAverageDefectCochain
      (matrixSUNAdjointModel Nc) U (extendZeroZeroCLM Omega phi))
  let R := restrictOneCLM (𝔤 := SUNLieCoord Nc) OmegaC
    (cmp99SourceCoarseTransportRemainderCochain
      (matrixSUNAdjointModel Nc) U V (extendZeroZeroCLM Omega phi))
  have hdef : ‖D‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
        ‖cmp89SourceNeumannRegionalRawD0 Omega
          (matrixSUNAdjointModel Nc) U phi‖ ^ 2 := by
    simpa only [D, OmegaC] using
      norm_restrictOne_cmp99SourceParallelAverageDefectCochain_sq_le_raw
        Omega (matrixSUNAdjointModel Nc) U phi
  have hrem : ‖R‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2 := by
    simpa only [R, OmegaC] using
      norm_restrictOne_cmp99SourceCoarseTransportRemainderCochain_sq_le
        Omega U V phi epsilonFine epsilonCoarse epsilonFine_nonneg
          epsilonCoarse_nonneg fine_small coarse_small
  dsimp only
  rw [cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_eq_twoSpecies
    Omega hOmega (matrixSUNAdjointModel Nc) U V spacing phi]
  rw [map_add]
  change ‖(((M : ℝ) * spacing)⁻¹) • (D + R)‖ ^ 2 ≤ _
  rw [norm_smul, mul_pow]
  have htri := norm_add_sq_le_two D R
  calc
    ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 * ‖D + R‖ ^ 2 ≤
        ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
          (2 * ‖D‖ ^ 2 + 2 * ‖R‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htri (sq_nonneg _)
    _ ≤ ‖((M : ℝ) * spacing)⁻¹‖ ^ 2 *
        (2 * (cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
            ‖cmp89SourceNeumannRegionalRawD0 Omega
              (matrixSUNAdjointModel Nc) U phi‖ ^ 2) +
          2 * (cmp99SourceBlockAverageWeight M d *
            (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
              epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdef (by positivity))
        (mul_le_mul_of_nonneg_left hrem (by positivity))
    _ = _ := by
      unfold cmp89SourceNeumannOneStepDefectCoefficient
      ring

/-- Physical specialization of the literal derivative feedback.  The
derivative coefficient is exactly `2 * M^{-d}`; the field coefficient is
exactly the same block mass times the named dimensionless `Ubar` budget. -/
theorem norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le_physical_feedback
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (etaFine etaCoarse : ℝ)
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ spacing * etaFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          ((M : ℝ) * spacing) * etaCoarse) :
    let psi := cmp99SourceTransportedBlockAverageCLM Omega
      (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U) phi
    ‖cmp89SourceNeumannRegionalCovariantD0CLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (matrixSUNAdjointModel Nc) V ((M : ℝ) * spacing) psi‖ ^ 2 ≤
      cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M *
          ‖cmp89SourceNeumannRegionalCovariantD0CLM Omega
            (matrixSUNAdjointModel Nc) U spacing phi‖ ^ 2 +
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
          d M etaFine etaCoarse * ‖phi‖ ^ 2 := by
  have hs : spacing ≠ 0 := ne_of_gt hspacing
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMs : (M : ℝ) * spacing ≠ 0 := mul_ne_zero hM hs
  have hepsFine : 0 ≤ spacing * etaFine :=
    mul_nonneg hspacing.le etaFine_nonneg
  have hepsCoarse : 0 ≤ ((M : ℝ) * spacing) * etaCoarse := by positivity
  have hraw :=
    norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le_raw_feedback
      Omega hOmega U V hs phi (spacing * etaFine)
        (((M : ℝ) * spacing) * etaCoarse) hepsFine hepsCoarse
          fine_small coarse_small
  rw [norm_cmp89SourceNeumannRegionalRawD0_sq_eq_spacing_sq_mul
    Omega (matrixSUNAdjointModel Nc) U hs phi] at hraw
  rw [cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling
    (d := d) (M := M) hs] at hraw
  have hcancel :
      ‖(((M : ℝ) * spacing)⁻¹)‖ ^ 2 * (M : ℝ) ^ 2 * spacing ^ 2 = 1 := by
    rw [Real.norm_eq_abs, sq_abs, inv_pow]
    field_simp
  have hderiv :
      ‖(((M : ℝ) * spacing)⁻¹)‖ ^ 2 *
          (2 * cmp99SourceBlockAverageWeight M d * (M : ℝ) ^ 2 *
            (spacing ^ 2 *
              ‖cmp89SourceNeumannRegionalCovariantD0CLM Omega
                (matrixSUNAdjointModel Nc) U spacing phi‖ ^ 2)) =
        2 * cmp99SourceBlockAverageWeight M d *
          ‖cmp89SourceNeumannRegionalCovariantD0CLM Omega
            (matrixSUNAdjointModel Nc) U spacing phi‖ ^ 2 := by
    calc
      _ = 2 * cmp99SourceBlockAverageWeight M d *
          (‖(((M : ℝ) * spacing)⁻¹)‖ ^ 2 *
            (M : ℝ) ^ 2 * spacing ^ 2) *
          ‖cmp89SourceNeumannRegionalCovariantD0CLM Omega
            (matrixSUNAdjointModel Nc) U spacing phi‖ ^ 2 := by ring
      _ = _ := by rw [hcancel]; ring
  unfold cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient
    cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
  calc
    _ ≤ _ := hraw
    _ = _ := by rw [hderiv]

/-- The physical two-scale Neumann Poincare producer after the literal
derivative-feedback theorem is installed.  Its only remaining analytic input
is the displayed strict scalar contraction for the explicit field-feedback
coefficient. -/
theorem cmp89SourceNeumann_twoScale_quantitativePoincare_of_physical_feedback
    {N'' : ℕ} [NeZero N'']
    (Omega : ActiveGaugeRegion d (M * (M * N'')))
    (hOmega : Omega.BlockSaturated)
    (hOmegaC :
      (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega).BlockSaturated)
    (U : PhysicalGaugeBackground d (M * (M * N'')) Nc)
    (V : PhysicalGaugeBackground d (M * N'') Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (etaFine etaCoarse : ℝ)
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * (M * N'')),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ spacing * etaFine)
    (coarse_small : ∀ b : PhysicalBond d (M * N''),
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          ((M : ℝ) * spacing) * etaCoarse)
    (feedback_small :
      cmp89SourceNeumannOneScalePoincareConstant d M spacing *
        cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing) *
        cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
          d M etaFine etaCoarse < 1) :
    CMP89SourceNeumannRegionalPoincare
      Omega (matrixSUNAdjointModel Nc) U
      ((cmp99SourceTransportedBlockAverageCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega)
          (cmp99SourceWeightedPhysicalTransport
            (matrixSUNAdjointModel Nc) V)).comp
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport
            (matrixSUNAdjointModel Nc) U)))
      spacing
      (cmp89SourceNeumannTwoLevelPoincareConstant
        (cmp89SourceNeumannOneScalePoincareConstant d M spacing)
        (cmp89SourceNeumannOneScalePoincareConstant d M
          ((M : ℝ) * spacing))
        (cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M)
        (cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
          d M etaFine etaCoarse)) := by
  apply cmp89SourceNeumann_twoScale_quantitativePoincare_of_derivative_feedback
    Omega hOmega hOmegaC U V (ne_of_gt hspacing)
      (cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient d M)
      (cmp89SourceNeumannPhysicalFieldFeedbackCoefficient
        d M etaFine etaCoarse)
  · exact cmp89SourceNeumannPhysicalDerivativeFeedbackCoefficient_nonneg d M
  · intro phi
    exact
      norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le_physical_feedback
        Omega hOmega U V hspacing phi etaFine etaCoarse etaFine_nonneg
          etaCoarse_nonneg fine_small coarse_small
  · exact feedback_small

end

end YangMills.RG
