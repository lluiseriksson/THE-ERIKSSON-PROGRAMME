import YangMills.RG.BalabanCMP99SourceActiveRegionTerminalBlockDiameter
import YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanionPrecision
import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

Exact finite-range and exponential-kernel budget for the literal
full-companion precision.  The counting coefficient remains literal and is
not identified with the generated-physical mass parameter.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Exact volume-independent norm budget for the literal full-companion
precision. -/
noncomputable def cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) : ℝ :=
  4 * d / spacing ^ 2 +
    |cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd hM rho
      spacing epsilon background chain fineSmall|

theorem cmp99SourceActiveRegionFullCompanionPrecisionUpperBound_pos
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    0 < cmp99SourceActiveRegionFullCompanionPrecisionUpperBound regions hd hM
      rho spacing epsilon background chain fineSmall := by
  unfold cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  have : 0 < 4 * (d : ℝ) / spacing ^ 2 := by positivity
  positivity

/-- The literal full-companion `Qprime†Qprime` has terminal-block range. -/
theorem cmp99SourceActiveRegionFullCompanion_QprimeMass_finiteRange
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho
      spacing epsilon background chain fineSmall
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
      (g := SUNLieCoord Nc) (T.Qprime.adjoint.comp T.Qprime)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1) := by
  let companion := cmp99SourceActiveRegionFullCompanion regions
  let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho
    spacing epsilon background chain fineSmall
  change FinitePiLpFiniteRange
    (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
    (g := SUNLieCoord Nc) (T.Qprime.adjoint.comp T.Qprime)
    (fun x y => finBoxDist x.1 y.1) (M ^ depth - 1)
  simpa [T, companion, cmp99SourceActiveRegionFullCompanionTower] using
    (companion.large.QprimeMass_finiteRange_terminalBlock hd hM rho spacing
      epsilon background chain fineSmall)

/-- Operator norm of the literal full-companion precision, with the
Laplacian and mass budgets exposed separately until the last inequality. -/
theorem norm_cmp99SourceActiveRegionFullCompanionPrecision_le
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖cmp99SourceActiveRegionFullCompanionPrecision regions hd hM rho spacing
      epsilon background chain fineSmall‖ ≤
      cmp99SourceActiveRegionFullCompanionPrecisionUpperBound regions hd hM
        rho spacing epsilon background chain fineSmall := by
  let companion := cmp99SourceActiveRegionFullCompanion regions
  let T := cmp99SourceActiveRegionFullCompanionTower regions hd hM rho
    spacing epsilon background chain fineSmall
  let b := cmp99SourceActiveRegionFullCompanionCountingCoefficient regions hd
    hM rho spacing epsilon background chain fineSmall
  have hQ : ‖T.Qprime‖ ≤ 1 := by
    simpa [T, companion, cmp99SourceActiveRegionFullCompanionTower] using
      (companion.large.norm_weightedQprimeTower_Qprime_le_one hd hM rho
        hspacing background chain fineSmall)
  have hDelta := norm_cmp99ActiveRegionSourceCovariantLaplacian_le
    (cmp99SourceFullActiveRegion d N) rho background hspacing
  rw [cmp99SourceActiveRegionFullCompanionPrecision, cmp99SourceGaugePrecision]
  unfold cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
  change ‖cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99SourceFullActiveRegion d N) rho background spacing +
      b • (T.Qprime.adjoint.comp T.Qprime)‖ ≤
    4 * d / spacing ^ 2 + |b|
  calc
    ‖cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99SourceFullActiveRegion d N) rho background spacing +
        b • (T.Qprime.adjoint.comp T.Qprime)‖ ≤
      ‖cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99SourceFullActiveRegion d N) rho background spacing‖ +
        ‖b • (T.Qprime.adjoint.comp T.Qprime)‖ := norm_add_le _ _
    _ ≤ 4 * d / spacing ^ 2 + |b| * ‖T.Qprime‖ ^ 2 := by
      rw [norm_smul, ContinuousLinearMap.norm_adjoint_comp_self,
        Real.norm_eq_abs]
      simpa only [pow_two] using add_le_add hDelta
        (le_refl (|b| * (‖T.Qprime‖ * ‖T.Qprime‖)))
    _ ≤ 4 * d / spacing ^ 2 + |b| := by
      have hQsq : ‖T.Qprime‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg T.Qprime]
      exact add_le_add_right
        (by simpa using mul_le_mul_of_nonneg_left hQsq (abs_nonneg b)) _

/-- Entrywise kernel bound for the literal full-companion precision. -/
theorem cmp99SourceActiveRegionFullCompanionPrecision_kernelBound
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpKernelBound
      (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
      (g := SUNLieCoord Nc)
      (cmp99SourceActiveRegionFullCompanionPrecision
        (d := d) (M := M) (N := N) (Nc := Nc)
        (Omega := Omega) (depth := depth)
        regions hd hM rho spacing epsilon background chain fineSmall)
      (fun _ _ =>
        cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
          (d := d) (M := M) (N := N) (Nc := Nc)
          (Omega := Omega) (depth := depth)
          regions hd hM rho spacing epsilon background chain fineSmall) := by
  apply finitePiLpKernelBound_of_opNorm_le
    (iota := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
    (g := SUNLieCoord Nc)
  exact norm_cmp99SourceActiveRegionFullCompanionPrecision_le
    (d := d) (M := M) (N := N) (Nc := Nc)
    (Omega := Omega) (depth := depth)
    regions hd hM rho hspacing background chain fineSmall

/-- The literal full-companion precision has the conservative common radius
`M^depth`, dominating the one-link Laplacian and terminal-block mass. -/
theorem cmp99SourceActiveRegionFullCompanionPrecision_finiteRange
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
      (g := SUNLieCoord Nc)
      (cmp99SourceActiveRegionFullCompanionPrecision
        (d := d) (M := M) (N := N) (Nc := Nc)
        (Omega := Omega) (depth := depth)
        regions hd hM rho spacing epsilon background chain fineSmall)
      (fun x y => finBoxDist x.1 y.1) (M ^ depth) := by
  intro source target v hfar
  have hpowPos : 0 < M ^ depth := pow_pos (NeZero.pos M) _
  have hlapFar : 1 < finBoxDist target.1 source.1 := by omega
  have hlap := cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
    (cmp99SourceFullActiveRegion d N) rho background spacing source target v
    hlapFar
  have hmassFar : M ^ depth - 1 < finBoxDist target.1 source.1 := by omega
  have hmass := cmp99SourceActiveRegionFullCompanion_QprimeMass_finiteRange
    (d := d) (M := M) (N := N) (Nc := Nc)
    (Omega := Omega) (depth := depth)
    regions hd hM rho spacing epsilon background chain fineSmall
      source target v hmassFar
  rw [cmp99SourceActiveRegionFullCompanionPrecision, cmp99SourceGaugePrecision]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [hlap, hmass]
  simp

/-- Finite range plus the literal kernel budget gives exact per-depth
exponential localization of the full-companion precision. -/
theorem cmp99SourceActiveRegionFullCompanionPrecision_exponentialKernelBound
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing)
    (hrate : 0 < rate) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpExponentialKernelBound
      (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
      (g := SUNLieCoord Nc)
      (cmp99SourceActiveRegionFullCompanionPrecision
        (d := d) (M := M) (N := N) (Nc := Nc)
        (Omega := Omega) (depth := depth)
        regions hd hM rho spacing epsilon background chain fineSmall)
      (fun x y => finBoxDist x.1 y.1)
      (cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
          (d := d) (M := M) (N := N) (Nc := Nc)
          (Omega := Omega) (depth := depth)
          regions hd hM rho spacing epsilon background chain fineSmall *
        Real.exp (rate * (M ^ depth : ℕ)))
      rate := by
  apply finitePiLpTypedExponentialKernelBound_of_finiteRange
    (ι := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
    (κ := ActiveGaugeRegion.Site (cmp99SourceFullActiveRegion d N))
    (g := SUNLieCoord Nc)
    (beta := cmp99SourceActiveRegionFullCompanionPrecisionUpperBound
      (d := d) (M := M) (N := N) (Nc := Nc)
      (Omega := Omega) (depth := depth)
      regions hd hM rho spacing epsilon background chain fineSmall)
    (R := M ^ depth)
  · exact (cmp99SourceActiveRegionFullCompanionPrecisionUpperBound_pos
      (d := d) (M := M) (N := N) (Nc := Nc)
      (Omega := Omega) (depth := depth)
      regions hd hM rho hspacing background chain fineSmall).le
  · exact hrate
  · exact cmp99SourceActiveRegionFullCompanionPrecision_finiteRange
      (d := d) (M := M) (N := N) (Nc := Nc)
      (Omega := Omega) (depth := depth)
      regions hd hM rho spacing epsilon background chain fineSmall
  · exact cmp99SourceActiveRegionFullCompanionPrecision_kernelBound
      (d := d) (M := M) (N := N) (Nc := Nc)
      (Omega := Omega) (depth := depth)
      regions hd hM rho hspacing background chain fineSmall

end

end YangMills.RG
