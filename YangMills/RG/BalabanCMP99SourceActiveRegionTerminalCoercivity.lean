import YangMills.RG.BalabanCMP85SourcePrefixGreen
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime
import YangMills.RG.BalabanCMP99SourceMassWeights

/-!
# Coercivity of the literal terminal precision on a typed source-region chain

This module closes the positive-depth algebraic part of the regional
coercivity bridge.  The covariant Laplacian, the retained `Qprime`, and the
Poincare inequality are generated from the same typed source-region chain.
No operator, Green function, or coercivity witness is accepted from a caller.

`BalabanCMP99SourceGeneratedPhysicalPrecision` already proves the analogous
statement for the canonical iterated-lift chain after normalizing its
derivative coefficient to one.  The point here is different: the selected
C6d source region is an arbitrary typed `CMP99SourceActiveRegionChain`, and
the counting coefficient must remain the literal Eq. (3.60) coefficient so
that the weighted/counting real-slice dictionary can consume it unchanged.

Depth zero is deliberately excluded from this theorem because the generated
fine-energy coefficient is definitionally zero there.  Its terminal
`Qprime` is the identity and requires a separate exact base-case theorem,
not a fictitious positive energy coefficient.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

/-- Exact positive-depth floor produced by the absorbed source Poincare
inequality for a literal counting-Hilbert coefficient `b`. -/
noncomputable def cmp99SourceActiveRegionTerminalCoercivity
    (d M depth : ℕ) (spacing epsilon b : ℝ) : ℝ :=
  (1 - cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) *
    min (cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon)⁻¹
      (b * (cmp99OneScaleBlockPoincareConstant d M ^ depth)⁻¹)

theorem cmp99SourceActiveRegionTerminalCoercivity_pos
    (hdepth : 0 < depth) {spacing epsilon b : ℝ}
    (hspacing : 0 < spacing) (hb : 0 < b)
    (hsmall :
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    0 < cmp99SourceActiveRegionTerminalCoercivity
      d M depth spacing epsilon b := by
  unfold cmp99SourceActiveRegionTerminalCoercivity
  exact twoWeightPoincare_coercivityConstant_pos
    (cmp99SourcePoincareEnergyCoeff_pos hdepth hspacing) hsmall
    (cmp99OneScaleBlockPoincareConstant_pow_pos depth) hb

/-- At depth zero the generated terminal average is exactly the identity, so
the counting coefficient itself is a coercivity floor.  Its strict positivity
is a separate scalar fact.  This is the honest base case excluded from the
positive-depth quotient above. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionTerminalPrecision_zero
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon b : ℝ}
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := regions.weightedQprimeTower hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background spacing)
        T.Qprime b)
      b := by
  cases regions with
  | stop Omega =>
      dsimp only [CMP99SourceActiveRegionChain.weightedQprimeTower,
        CMP99SourceWeightedRegionalTower.stop]
      intro phi
      rw [inner_cmp99SourceGaugePrecision,
        ContinuousLinearMap.id_apply]
      exact le_add_of_nonneg_left
        (by
          simpa only [inner_cmp99ActiveRegionSourceCovariantLaplacian] using
            (sq_nonneg ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
              (matrixSUNAdjointModel Nc) background spacing phi‖))

/-- The terminal source precision on an arbitrary typed source-region chain
is coercive with the exact robust floor.  All analytic inputs come from that
same generated regional chain. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionTerminalPrecision
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    {spacing epsilon b : ℝ} (hspacing : 0 < spacing) (hb : 0 < b)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall :
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := regions.weightedQprimeTower hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background spacing)
        T.Qprime b)
      (cmp99SourceActiveRegionTerminalCoercivity
        d M depth spacing epsilon b) := by
  letI : NeZero N := regions.neZero
  dsimp only
  let D := cmp99ActiveRegionSourceCovariantLaplacian Omega
    (matrixSUNAdjointModel Nc) background spacing
  let T := regions.weightedQprimeTower hd hM
    (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
  let A := cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon
  let B := cmp99SourcePoincareErrorCoeff d M depth spacing epsilon
  let C := cmp99OneScaleBlockPoincareConstant d M ^ depth
  have hA : 0 < A := cmp99SourcePoincareEnergyCoeff_pos hdepth hspacing
  have hC : 0 < C := cmp99OneScaleBlockPoincareConstant_pow_pos depth
  have hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi) := by
    intro phi
    simpa only [D, inner_cmp99ActiveRegionSourceCovariantLaplacian] using
      (sq_nonneg ‖cmp99ActiveRegionSourceCovariantD0CLM Omega
        (matrixSUNAdjointModel Nc) background spacing phi‖)
  have hraw : ∀ phi,
      (1 - B) * ‖phi‖ ^ 2 ≤
        A * inner ℝ phi (D phi) + C * ‖T.Qprime phi‖ ^ 2 := by
    intro phi
    have habs := regions.norm_sq_le_absorbed_poincare hd hM hspacing
      background chain fineSmall phi hsmall
    rw [regions.scaledGradientEnergy_zero hd hM spacing epsilon background
        chain fineSmall phi,
      regions.terminalFieldNormSq_eq_weightedQprimeTower hd hM spacing
        epsilon background chain fineSmall phi] at habs
    have hmul := (le_div_iff₀ (sub_pos.mpr hsmall)).mp habs
    simpa only [A, B, C, D, T,
      inner_cmp99ActiveRegionSourceCovariantLaplacian, mul_comm] using hmul
  simpa only [D, T, A, B, C,
    cmp99SourceActiveRegionTerminalCoercivity] using
      (isCoerciveCLM_of_twoWeightPoincare D T.Qprime hA hC hb
        hDnonneg hraw)

/-- Counting-Hilbert coefficient corresponding to the printed weighted
coefficient `a_j * terminalSpacing⁻²`.  The terminal/fine volume ratio is
mandatory: omitting it is the same convention error as applying `M⁻⁴`
twice. -/
noncomputable def cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
    (T : CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing)
    (a : ℝ) : ℝ :=
  a * T.terminalSpacing⁻¹ ^ 2 *
    (T.terminalSpacing ^ d / spacing ^ d)

theorem cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_pos
    (T : CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing)
    {a : ℝ} (ha : 0 < a) (hspacing : 0 < spacing)
    (hterminal : 0 < T.terminalSpacing) :
    0 < cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T a := by
  unfold cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
  exact mul_pos (mul_pos ha (pow_pos (inv_pos.mpr hterminal) 2))
    (div_pos (pow_pos hterminal d) (pow_pos hspacing d))

/-- Multiplying the counting coefficient by the exact counting-to-weighted
adjoint ratio recovers the printed coefficient `a_j * terminalSpacing⁻²`.
This equality is the scalar convention gate used by the later C6d wrapper. -/
theorem cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_toWeighted
    (T : CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing)
    (a : ℝ) (hspacing : spacing ≠ 0)
    (hterminal : T.terminalSpacing ≠ 0) :
    cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T a *
        (spacing ^ d / T.terminalSpacing ^ d) =
      a * T.terminalSpacing⁻¹ ^ 2 := by
  unfold cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
  field_simp [hspacing, hterminal] <;> ring

/-- Source-fixed positive-depth floor.  CMP99 Theorem 3.1 fixes the initial
averaging coefficient to one, Eq. (3.24) generates `a_j`, and the exact
terminal/fine volume ratio converts its printed weighted coefficient to the
counting-Hilbert coefficient used by the regional precision. -/
noncomputable def cmp99SourceActiveRegionTerminalPhysicalCoercivity
    (T : CMP99SourceWeightedRegionalTower (g := SUNLieCoord Nc) Omega spacing)
    (M depth : ℕ) (epsilon : ℝ) : ℝ :=
  cmp99SourceActiveRegionTerminalCoercivity d M depth spacing epsilon
    (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
      (cmp99SourceMassParameter 1 (M : ℝ) depth))

/-- The source-fixed floor is strictly positive at positive depth. -/
theorem cmp99SourceActiveRegionTerminalPhysicalCoercivity_pos
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall :
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := regions.weightedQprimeTower hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    0 < cmp99SourceActiveRegionTerminalPhysicalCoercivity
      T M depth epsilon := by
  dsimp only
  let T := regions.weightedQprimeTower hd hM
    (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (NeZero.pos M)
  have haj : 0 < cmp99SourceMassParameter 1 (M : ℝ) depth :=
    cmp99SourceMassParameter_pos (by norm_num) hMreal depth
  have hterminal : 0 < T.terminalSpacing := by
    rw [regions.weightedQprimeTower_terminalSpacing]
    exact mul_pos (pow_pos hMreal depth) hspacing
  have hb :
      0 < cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
        (cmp99SourceMassParameter 1 (M : ℝ) depth) :=
    cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_pos
      T haj hspacing hterminal
  unfold cmp99SourceActiveRegionTerminalPhysicalCoercivity
  exact cmp99SourceActiveRegionTerminalCoercivity_pos
    hdepth hspacing hb hsmall

/-- At depth zero the source recurrence gives `a_0 = 1`, but the printed
coefficient is still `spacing⁻²`.  The volume ratio is one; the coefficient
must not be silently replaced by one. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionTerminalPhysicalPrecision_zero
    (regions : CMP99SourceActiveRegionChain d M N Omega 0)
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    {spacing epsilon : ℝ}
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc 0 epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := regions.weightedQprimeTower hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background spacing)
        T.Qprime
        (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
          (cmp99SourceMassParameter 1 (M : ℝ) 0)))
      (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
        (cmp99SourceMassParameter 1 (M : ℝ) 0)) := by
  dsimp only
  exact
    (isCoerciveCLM_cmp99SourceActiveRegionTerminalPrecision_zero
      regions hd hM background chain fineSmall
      (b := cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient
        (regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
          spacing epsilon background chain fineSmall)
        (cmp99SourceMassParameter 1 (M : ℝ) 0)))

/-- Source-facing positive-depth coercivity producer.  The regional chain,
background, terminal average, and coefficient are all literal source data;
the caller supplies only the scalar smallness condition already present in
the absorbed Poincare estimate. -/
theorem isCoerciveCLM_cmp99SourceActiveRegionTerminalPhysicalPrecision
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (hdepth : 0 < depth)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall :
      cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := regions.weightedQprimeTower hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
    IsCoerciveCLM
      (cmp99SourceGaugePrecision
        (cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background spacing)
        T.Qprime
        (cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
          (cmp99SourceMassParameter 1 (M : ℝ) depth)))
      (cmp99SourceActiveRegionTerminalPhysicalCoercivity
        T M depth epsilon) := by
  dsimp only
  let T := regions.weightedQprimeTower hd hM
    (matrixSUNAdjointModel Nc) spacing epsilon background chain fineSmall
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (NeZero.pos M)
  have haj : 0 < cmp99SourceMassParameter 1 (M : ℝ) depth :=
    cmp99SourceMassParameter_pos (by norm_num) hMreal depth
  have hterminal : 0 < T.terminalSpacing := by
    rw [regions.weightedQprimeTower_terminalSpacing]
    exact mul_pos (pow_pos hMreal depth) hspacing
  have hb :
      0 < cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient T
        (cmp99SourceMassParameter 1 (M : ℝ) depth) :=
    cmp99SourceActiveRegionTerminalPhysicalCountingCoefficient_pos
      T haj hspacing hterminal
  unfold cmp99SourceActiveRegionTerminalPhysicalCoercivity
  exact isCoerciveCLM_cmp99SourceActiveRegionTerminalPrecision regions hd hM
    hdepth hspacing hb background chain fineSmall hsmall

end

end YangMills.RG
