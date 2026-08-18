import tmp.P2SourceCoefficientCoercivity

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only elaboration target for Step 8b.24/P2b.

The source coefficient multiplying the weighted adjoint and the coefficient
multiplying Lean's counting adjoint are intentionally distinct.  This file is
not compiler evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Counting-Hilbert presentation of CMP85 (2.21).

If `bWeighted` is the printed coefficient and `bCount` is its coefficient
after converting the source-weighted adjoint to Lean's counting adjoint, the
second term is `bWeighted*bCount`, not either square separately. -/
noncomputable def scratch_cmp85EffectiveQuadratic
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bWeighted bCount : ℝ) : F →L[ℝ] F :=
  bWeighted • ContinuousLinearMap.id ℝ F -
    (bWeighted * bCount) • (Q.comp (G.comp Q.adjoint))

/-- Symmetry of the effective quadratic is inherited from the internally
constructed Green operator. -/
theorem scratch_cmp85EffectiveQuadratic_isSymmetric
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bWeighted bCount : ℝ) (hG : G.IsSymmetric) :
    (scratch_cmp85EffectiveQuadratic Q G bWeighted bCount).IsSymmetric := by
  have hmiddle : ∀ x y,
      inner ℝ (Q (G (Q.adjoint x))) y =
        inner ℝ x (Q (G (Q.adjoint y))) := by
    intro x y
    calc
      inner ℝ (Q (G (Q.adjoint x))) y =
          inner ℝ (G (Q.adjoint x)) (Q.adjoint y) :=
        (ContinuousLinearMap.adjoint_inner_right Q _ _).symm
      _ = inner ℝ (Q.adjoint x) (G (Q.adjoint y)) :=
        hG _ _
      _ = inner ℝ x (Q (G (Q.adjoint y))) :=
        ContinuousLinearMap.adjoint_inner_left Q _ _
  intro x y
  unfold scratch_cmp85EffectiveQuadratic
  change inner ℝ
      (bWeighted • x -
        (bWeighted * bCount) • Q (G (Q.adjoint x))) y =
    inner ℝ x
      (bWeighted • y -
        (bWeighted * bCount) • Q (G (Q.adjoint y)))
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, hmiddle]

/-- The fine field selected by one coarse test field in the Schur
completion. -/
noncomputable def scratch_cmp85SchurFineField
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bCount : ℝ) (eta : F) : H :=
  bCount • G (Q.adjoint eta)

/-- The inverse law for `D + bCount*Q^*Q` gives the exact Euler equation for
the internally selected fine field.  This is derived here rather than passed
as a completed-square premise. -/
theorem scratch_cmp85SchurFineField_euler
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (bCount : ℝ)
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    D (scratch_cmp85SchurFineField Q G bCount eta) =
      bCount • Q.adjoint
        (eta - Q (scratch_cmp85SchurFineField Q G bCount eta)) := by
  have hpoint := congrArg
    (fun A : H →L[ℝ] H => A (Q.adjoint eta)) hKG
  change cmp99SourceGaugePrecision D Q bCount (G (Q.adjoint eta)) =
    Q.adjoint eta at hpoint
  unfold scratch_cmp85SchurFineField
  simp only [map_smul, map_sub, smul_sub]
  simp only [cmp99SourceGaugePrecision,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply] at hpoint
  apply eq_sub_iff_add_eq.mpr
  simpa only [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun x : H => bCount • x) hpoint

/-- Exact completed-square identity for CMP85 (2.21) in counting
coordinates.  The factor `bWeighted/bCount` is precisely the fine/coarse
volume ratio after the physical specialization. -/
set_option linter.unusedVariables false in
theorem scratch_inner_cmp85EffectiveQuadratic_eq_completedSquare
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    {bWeighted bCount : ℝ} (hbCount : bCount ≠ 0)
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    let phi := scratch_cmp85SchurFineField Q G bCount eta
    inner ℝ eta
        (scratch_cmp85EffectiveQuadratic Q G bWeighted bCount eta) =
      (bWeighted / bCount) * inner ℝ phi (D phi) +
        bWeighted * ‖eta - Q phi‖ ^ 2 := by
  dsimp only
  let phi := scratch_cmp85SchurFineField Q G bCount eta
  have hEuler := scratch_cmp85SchurFineField_euler
    D Q G bCount hKG eta
  have hEnergy :
      inner ℝ phi (D phi) =
        bCount * inner ℝ (Q phi) (eta - Q phi) := by
    rw [hEuler, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
  simp only [scratch_cmp85EffectiveQuadratic,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, inner_smul_right]
  change _ = (bWeighted / bCount) * inner ℝ phi (D phi) + _
  rw [hEnergy]
  have hQphi :
      Q phi = bCount • Q (G (Q.adjoint eta)) := by
    unfold phi scratch_cmp85SchurFineField
    rw [map_smul]
  rw [hQphi]
  simp only [inner_smul_left, conj_trivial]
  rw [← real_inner_self_eq_norm_sq, inner_sub_right, inner_sub_right]
  simp only [inner_sub_left, inner_smul_left, inner_smul_right, conj_trivial]
  field_simp [hbCount]
  rw [real_inner_comm eta (Q (G (Q.adjoint eta)))]
  ring

/-- Nonnegativity of the effective quadratic form follows from the exact
completed square.  No lower bound for the effective operator is supplied. -/
theorem scratch_inner_cmp85EffectiveQuadratic_nonneg
    {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    {bWeighted bCount : ℝ} (hbWeighted : 0 < bWeighted)
    (hbCount : 0 < bCount)
    (hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi))
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    0 ≤ inner ℝ eta
      (scratch_cmp85EffectiveQuadratic Q G bWeighted bCount eta) := by
  rw [scratch_inner_cmp85EffectiveQuadratic_eq_completedSquare
    D Q G hbCount.ne' hKG eta]
  exact add_nonneg
    (mul_nonneg (div_nonneg hbWeighted.le hbCount.le)
      (hDnonneg (scratch_cmp85SchurFineField Q G bCount eta)))
    (mul_nonneg hbWeighted.le (sq_nonneg _))

/-! ## Source-facing positive-prefix specialization -/

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The printed weighted-adjoint presentation of (2.21) is exactly the
counting-Hilbert operator above.  The proof consumes the spacing dictionary;
it does not identify `bWeighted` with `bCount`. -/
theorem scratch_cmp85SourceEffectiveQuadratic_weighted_eq_counting
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {a : ℝ} (hspacing : 0 < spacing)
    (r : ScratchCMP85PositivePrefix depth) :
    let Q := (T.towerAt r.1).Qprime
    let bWeighted := scratch_cmp85SourcePrefixWeightedCoefficient T a r
    bWeighted • ContinuousLinearMap.id ℝ
        (T.towerAt r.1).TerminalSpace.carrier -
      bWeighted ^ 2 •
        (Q.comp (G.comp (T.towerAt r.1).weightedAdjoint)) =
      scratch_cmp85EffectiveQuadratic Q G bWeighted
        (scratch_cmp85SourcePrefixCountingCoefficient T a r) := by
  dsimp only
  have hterminal : 0 < (T.towerAt r.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val)
      hspacing
  have hbridge :=
    (T.towerAt r.1).adjoint_eq_spacingRatio_smul_weightedAdjoint
      hterminal.ne'
  have hscalar :
      scratch_cmp85SourcePrefixCountingCoefficient T a r *
          (spacing ^ d / (T.towerAt r.1).terminalSpacing ^ d) =
        scratch_cmp85SourcePrefixWeightedCoefficient T a r := by
    unfold scratch_cmp85SourcePrefixCountingCoefficient
    unfold scratch_cmp85SourcePrefixVolumeRatio
    field_simp [pow_ne_zero d hspacing.ne', pow_ne_zero d hterminal.ne']
  unfold scratch_cmp85EffectiveQuadratic
  apply ContinuousLinearMap.ext
  intro eta
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  rw [hbridge]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_assoc, hscalar]
  ring

/-- Source-generated positive-prefix effective quadratic of CMP85 (2.21).
The retained tower, Green operator and both coefficient conventions are
constructed internally. -/
noncomputable def scratch_cmp85SourceGeneratedEffectiveQuadratic
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :=
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  scratch_cmp85EffectiveQuadratic (T.towerAt r.1).Qprime
    (scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall r)
    (scratch_cmp85SourcePrefixWeightedCoefficient T a r)
    (scratch_cmp85SourcePrefixCountingCoefficient T a r)

/-- The generated effective quadratic has a nonnegative real quadratic
form, derived from the P2a inverse and the exact completed square. -/
theorem scratch_inner_cmp85SourceGeneratedEffectiveQuadratic_nonneg
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth)
    (eta : ((scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall).towerAt r.1).TerminalSpace.carrier) :
    0 ≤ inner ℝ eta
      (scratch_cmp85SourceGeneratedEffectiveQuadratic hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall r eta) := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let D := scratch_cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let Q := (T.towerAt r.1).Qprime
  let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  let bWeighted := scratch_cmp85SourcePrefixWeightedCoefficient T a r
  let bCount := scratch_cmp85SourcePrefixCountingCoefficient T a r
  have hbWeighted : 0 < bWeighted :=
    scratch_cmp85SourcePrefixWeightedCoefficient_pos T ha hspacing r
  have hbCount : 0 < bCount :=
    scratch_cmp85SourcePrefixCountingCoefficient_pos T ha hspacing r
  have hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi) := by
    intro phi
    simpa only [D, scratch_inner_cmp85BareMassPrecision,
      inner_cmp99ActiveRegionSourceCovariantLaplacian] using
      add_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖))
  have hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [D, Q, G, bCount, T,
      scratch_cmp85SourceGeneratedPrefixPrecision,
      scratch_cmp85SourceGeneratedPrefixTower] using
      scratch_cmp85SourceGeneratedPrefixPrecision_comp_green hd hM Omega0
        depth hspacing ha mass background0 chain fineSmall hsmall r
  simpa only [scratch_cmp85SourceGeneratedEffectiveQuadratic, T, Q, G,
    bWeighted, bCount] using
    scratch_inner_cmp85EffectiveQuadratic_nonneg D Q G hbWeighted hbCount
      hDnonneg hKG eta

/-- The generated source effective quadratic is symmetric, with no
caller-supplied Green symmetry premise. -/
theorem scratch_cmp85SourceGeneratedEffectiveQuadratic_isSymmetric
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    (scratch_cmp85SourceGeneratedEffectiveQuadratic hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r).IsSymmetric := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  apply scratch_cmp85EffectiveQuadratic_isSymmetric
  exact scratch_cmp85SourceGeneratedPrefixGreen_isSymmetric hd hM Omega0
    depth hspacing ha mass background0 chain fineSmall hsmall r

end

end YangMills.RG
