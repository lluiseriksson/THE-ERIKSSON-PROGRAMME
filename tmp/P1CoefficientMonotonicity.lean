import tmp.P0CanonicalPrefixTower

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only elaboration target for Step 8b.24/P1.

This file is intentionally outside the tracked import graph.  Its purpose is
to validate that prefix smallness follows from one terminal Poincare-error
budget without assuming monotonicity of the nonlinear `Ubar` radius map.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {d M : ℕ} [NeZero d] [NeZero M]

/-- Adjacent-depth monotonicity of the generated Poincare energy ledger. -/
theorem scratch_cmp99SourcePoincareEnergyCoeff_le_succ
    (depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon ≤
      cmp99SourcePoincareEnergyCoeff d M (depth + 1) spacing epsilon := by
  induction depth generalizing spacing epsilon with
  | zero =>
      simp only [cmp99SourcePoincareEnergyCoeff]
      exact cmp99SourcePoincareEnergyCoeff_nonneg d M 1 spacing epsilon
  | succ depth ih =>
      change
        cmp99OneScaleBlockPoincareConstant d M *
              (spacing ^ 2 +
                2 * cmp99SourceBlockAverageWeight M d *
                  cmp99SourcePoincareEnergyCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon)) ≤
          cmp99OneScaleBlockPoincareConstant d M *
              (spacing ^ 2 +
                2 * cmp99SourceBlockAverageWeight M d *
                  cmp99SourcePoincareEnergyCoeff d M (depth + 1)
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon))
      apply mul_le_mul_of_nonneg_left _
        (le_of_lt cmp99OneScaleBlockPoincareConstant_pos)
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left
        (ih ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon))
        (mul_nonneg (by norm_num)
          (cmp99SourceBlockAverageWeight_nonneg M d))

/-- Full depth monotonicity of the generated Poincare energy ledger. -/
theorem scratch_cmp99SourcePoincareEnergyCoeff_monotone
    (spacing epsilon : ℝ) :
    Monotone (fun depth ↦
      cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon) :=
  monotone_nat_of_le_succ fun depth ↦
    scratch_cmp99SourcePoincareEnergyCoeff_le_succ depth spacing epsilon

/-- Adjacent-depth monotonicity of the generated Poincare error ledger. -/
theorem scratch_cmp99SourcePoincareErrorCoeff_le_succ
    (depth : ℕ) (spacing epsilon : ℝ) :
    cmp99SourcePoincareErrorCoeff d M depth spacing epsilon ≤
      cmp99SourcePoincareErrorCoeff d M (depth + 1) spacing epsilon := by
  induction depth generalizing spacing epsilon with
  | zero =>
      simp only [cmp99SourcePoincareErrorCoeff]
      exact cmp99SourcePoincareErrorCoeff_nonneg d M 1 spacing epsilon
  | succ depth ih =>
      change
        cmp99OneScaleBlockPoincareConstant d M *
              (cmp99SourcePoincareEnergyCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  cmp99SourceScaledGradientStepError d M epsilon spacing +
                cmp99SourcePoincareErrorCoeff d M depth
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  cmp99SourceBlockAverageWeight M d) ≤
          cmp99OneScaleBlockPoincareConstant d M *
              (cmp99SourcePoincareEnergyCoeff d M (depth + 1)
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  cmp99SourceScaledGradientStepError d M epsilon spacing +
                cmp99SourcePoincareErrorCoeff d M (depth + 1)
                    ((M : ℝ) * spacing)
                    (cmp99SourceUbarNextFineRadius d M epsilon) *
                  cmp99SourceBlockAverageWeight M d)
      apply mul_le_mul_of_nonneg_left _
        (le_of_lt cmp99OneScaleBlockPoincareConstant_pos)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (scratch_cmp99SourcePoincareEnergyCoeff_le_succ depth
            ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon))
          (cmp99SourceScaledGradientStepError_nonneg d M epsilon spacing)
      · exact mul_le_mul_of_nonneg_right
          (ih ((M : ℝ) * spacing)
            (cmp99SourceUbarNextFineRadius d M epsilon))
          (cmp99SourceBlockAverageWeight_nonneg M d)

/-- Full depth monotonicity of the generated Poincare error ledger. -/
theorem scratch_cmp99SourcePoincareErrorCoeff_monotone
    (spacing epsilon : ℝ) :
    Monotone (fun depth ↦
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) :=
  monotone_nat_of_le_succ fun depth ↦
    scratch_cmp99SourcePoincareErrorCoeff_le_succ depth spacing epsilon

/-- Every positive prefix has a strictly positive generated energy
coefficient.  Depth zero is deliberately excluded: its coefficient is
definitionally zero. -/
theorem scratch_cmp99SourcePoincareEnergyCoeff_pos
    {depth : ℕ} (hdepth : 0 < depth) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing) :
    0 < cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon := by
  have hbase :
      0 < cmp99SourcePoincareEnergyCoeff d M 1 spacing epsilon := by
    change 0 < cmp99OneScaleBlockPoincareConstant d M * spacing ^ 2
    exact mul_pos cmp99OneScaleBlockPoincareConstant_pos
      (pow_pos hspacing 2)
  exact hbase.trans_le
    (scratch_cmp99SourcePoincareEnergyCoeff_monotone
      (d := d) (M := M) spacing epsilon hdepth)

/-- The literal terminal coefficient `CP^j` is positive at every prefix. -/
theorem scratch_cmp99OneScaleBlockPoincareConstant_pow_pos
    (depth : ℕ) :
    0 < cmp99OneScaleBlockPoincareConstant d M ^ depth :=
  pow_pos cmp99OneScaleBlockPoincareConstant_pos depth

/-- One terminal smallness hypothesis discharges every prefix smallness
hypothesis; no family of scalar windows is accepted from the caller. -/
theorem scratch_cmp99SourcePoincareErrorCoeff_lt_of_le_depth
    {prefix depth : ℕ} (hprefix : prefix ≤ depth)
    {spacing epsilon : ℝ}
    (hterminal :
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    cmp99SourcePoincareErrorCoeff d M prefix spacing epsilon < 1 :=
  (scratch_cmp99SourcePoincareErrorCoeff_monotone
    (d := d) (M := M) spacing epsilon hprefix).trans_lt hterminal

variable {N Nc : ℕ} [NeZero N] [NeZero Nc]

/-- One terminal scalar budget gives the absorbed Poincare inequality at
every retained physical prefix, with the terminal term written using the
literal retained `Q'_r`.  The field remains on the original fine carrier. -/
theorem scratch_cmp99SourceGeneratedRetainedPhysicalTower_prefix_poincare
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : Fin (depth + 1))
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
      (SUNLieCoord Nc)) :
    let T := cmp99SourceGeneratedRetainedPhysicalTower hd hM
      (matrixSUNAdjointModel Nc) Omega depth spacing epsilon background chain
      fineSmall
    ‖phi‖ ^ 2 ≤
      (cmp99SourcePoincareEnergyCoeff d M r.val spacing epsilon *
            ‖cmp99ActiveRegionSourceCovariantD0CLM
              (cmp99IteratedLiftActiveRegion (M := M) Omega depth)
              (matrixSUNAdjointModel Nc) background spacing phi‖ ^ 2 +
          cmp99OneScaleBlockPoincareConstant d M ^ r.val *
            ‖(T.towerAt r).Qprime phi‖ ^ 2) /
        (1 - cmp99SourcePoincareErrorCoeff d M r.val spacing epsilon) := by
  dsimp only
  let regions :=
    cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega depth
  let regionsR := regions.takeFin r
  let chainR := chain.takeFin r
  have hrle : r.val ≤ depth := Nat.lt_succ_iff.mp r.isLt
  have hsmallR :
      cmp99SourcePoincareErrorCoeff d M r.val spacing epsilon < 1 :=
    scratch_cmp99SourcePoincareErrorCoeff_lt_of_le_depth hrle hsmall
  have hp := regionsR.norm_sq_le_absorbed_poincare hd hM hspacing
    background chainR fineSmall phi hsmallR
  rw [regionsR.scaledGradientEnergy_zero hd hM spacing epsilon background
      chainR fineSmall phi,
    regionsR.terminalFieldNormSq_eq_weightedQprimeTower hd hM spacing epsilon
      background chainR fineSmall phi] at hp
  have hprefix :=
    scratch_cmp99SourceGeneratedRetainedPhysicalTower_towerAt_eq_take
      hd hM (matrixSUNAdjointModel Nc) Omega depth spacing epsilon background
      chain fineSmall r
  rw [← hprefix] at hp
  exact hp

end

end YangMills.RG
