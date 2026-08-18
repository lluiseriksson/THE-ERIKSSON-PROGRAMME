import tmp.P2bEffectiveQuadratic

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only elaboration target for Step 8b.24/P2c.

This file isolates the finite-dimensional algebra of CMP85 (2.30).  The
source-facing producer must discharge `hZeroControl` from the generated
prefix Poincare theorem; it may not expose that implication to its caller.
Nothing in this file is compiler evidence or imported by the tracked tree.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-! ## One-step weighted/counting dictionary -/

/-- Printed coefficient of the one-step projector in CMP85 (2.30). -/
noncomputable def scratch_cmp85SourceStepWeightedCoefficient
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : Fin depth) : ℝ :=
  a * (T.towerAt k.succ).terminalSpacing⁻¹ ^ 2

/-- Counting-Hilbert coefficient of the same one-step projector.  The
factor `M^d` is the exact coarse/fine volume ratio. -/
noncomputable def scratch_cmp85SourceStepCountingCoefficient
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : Fin depth) : ℝ :=
  scratch_cmp85SourceStepWeightedCoefficient T a k * (M : ℝ) ^ d

theorem scratch_cmp85SourceStepWeightedCoefficient_pos
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    {a : ℝ} (ha : 0 < a) (hspacing : 0 < spacing) (k : Fin depth) :
    0 < scratch_cmp85SourceStepWeightedCoefficient T a k := by
  have hterminal : 0 < (T.towerAt k.succ).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos (by exact_mod_cast (NeZero.pos M)) k.succ.val)
      hspacing
  unfold scratch_cmp85SourceStepWeightedCoefficient
  exact mul_pos ha (pow_pos (inv_pos.mpr hterminal) 2)

theorem scratch_cmp85SourceStepCountingCoefficient_pos
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    {a : ℝ} (ha : 0 < a) (hspacing : 0 < spacing) (k : Fin depth) :
    0 < scratch_cmp85SourceStepCountingCoefficient T a k := by
  unfold scratch_cmp85SourceStepCountingCoefficient
  exact mul_pos
    (scratch_cmp85SourceStepWeightedCoefficient_pos T ha hspacing k)
    (pow_pos (by exact_mod_cast (NeZero.pos M)) d)

/-- Source-weighted adjoint of one generated retained step, expressed via
the exact one-step volume ratio and Lean's counting adjoint. -/
noncomputable def scratch_cmp85SourceStepWeightedAdjoint
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (k : Fin depth) :
    (T.towerAt k.succ).TerminalSpace.carrier →L[ℝ]
      (T.towerAt k.castSucc).TerminalSpace.carrier :=
  (M : ℝ) ^ d • (T.nextAverage k).adjoint

/-- The constructed one-step adjoint satisfies the two printed
lattice-spacing pairings.  This is the semantic dictionary that prevents the
preceding definition from being merely a convenient rescaling. -/
theorem scratch_cmp85SourceStepWeightedAdjoint_pairing
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (k : Fin depth)
    (phi : (T.towerAt k.castSucc).TerminalSpace.carrier)
    (eta : (T.towerAt k.succ).TerminalSpace.carrier) :
    cmp99SourceSpacingPairing d (T.towerAt k.succ).terminalSpacing
        (T.nextAverage k phi) eta =
      cmp99SourceSpacingPairing d
        (T.towerAt k.castSucc).terminalSpacing phi
        (scratch_cmp85SourceStepWeightedAdjoint T k eta) := by
  have hspacing :
      (T.towerAt k.succ).terminalSpacing =
        (M : ℝ) * (T.towerAt k.castSucc).terminalSpacing := by
    rw [T.towerAt_terminalSpacing, T.towerAt_terminalSpacing]
    simp only [Fin.succ_val, Fin.coe_castSucc]
    rw [pow_succ]
    ring
  rw [hspacing]
  unfold cmp99SourceSpacingPairing
  unfold scratch_cmp85SourceStepWeightedAdjoint
  rw [ContinuousLinearMap.smul_apply, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [mul_pow, conj_trivial]
  ring

/-- Exact equality between the printed weighted-adjoint term and its
counting-Hilbert presentation.  The scalar coefficients themselves are not
identified. -/
theorem scratch_cmp85SourceStepWeightedTerm_eq_counting
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (k : Fin depth) :
    scratch_cmp85SourceStepWeightedCoefficient T a k •
        ((scratch_cmp85SourceStepWeightedAdjoint T k).comp (T.nextAverage k)) =
      scratch_cmp85SourceStepCountingCoefficient T a k •
        ((T.nextAverage k).adjoint.comp (T.nextAverage k)) := by
  apply ContinuousLinearMap.ext
  intro eta
  unfold scratch_cmp85SourceStepWeightedAdjoint
  unfold scratch_cmp85SourceStepCountingCoefficient
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_smul]

/-- An absorbed Poincare inequality forces a field to vanish once its two
literal numerator terms vanish.  No coercivity constant is introduced. -/
theorem scratch_eq_zero_of_absorbedPoincare_numerator_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [Norm E]
    [NormedAddCommGroup F] [Norm F]
    {A B C energy : ℝ} {Q : E → F} {phi : E}
    (hPoincare : ‖phi‖ ^ 2 ≤
      (A * energy + C * ‖Q phi‖ ^ 2) / (1 - B))
    (hEnergy : energy = 0) (hQ : Q phi = 0) :
    phi = 0 := by
  have hnorm : ‖phi‖ ^ 2 ≤ 0 := by
    simpa [hEnergy, hQ] using hPoincare
  have hnormEq : ‖phi‖ ^ 2 = 0 :=
    le_antisymm hnorm (sq_nonneg ‖phi‖)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormEq)

/-- Physical zero-control implication required by P2c.  It is discharged
from the next retained prefix rather than accepted as a source-facing input.
The independent bare mass contributes only a nonnegative square. -/
theorem scratch_cmp85SourceGeneratedPrefix_zeroControl
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (k : Fin depth)
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (SUNLieCoord Nc))
    (hEnergy : inner ℝ phi
      (scratch_cmp85BareMassPrecision
        (cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
          (matrixSUNAdjointModel Nc) background0 spacing)
        mass phi) = 0)
    (hStep :
      let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
        spacing epsilon background0 chain fineSmall
      T.nextAverage k ((T.towerAt k.castSucc).Qprime phi) = 0) :
    phi = 0 := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let D0 := cmp99ActiveRegionSourceCovariantD0CLM
    (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
    (matrixSUNAdjointModel Nc) background0 spacing
  have hGradient : ‖D0 phi‖ ^ 2 = 0 := by
    rw [scratch_inner_cmp85BareMassPrecision,
      inner_cmp99ActiveRegionSourceCovariantLaplacian] at hEnergy
    have hgrad0 : 0 ≤ ‖D0 phi‖ ^ 2 := sq_nonneg _
    have hmass0 : 0 ≤ mass ^ 2 * ‖phi‖ ^ 2 :=
      mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖)
    have : ‖D0 phi‖ ^ 2 = 0 := by nlinarith
    exact this
  have hQnext : (T.towerAt k.succ).Qprime phi = 0 := by
    rw [T.Qprime_succ k, ContinuousLinearMap.comp_apply]
    exact hStep
  have hPoincare :=
    scratch_cmp99SourceGeneratedRetainedPhysicalTower_prefix_poincare
      hd hM Omega0 depth hspacing background0 chain fineSmall hsmall
        k.succ phi
  apply scratch_eq_zero_of_absorbedPoincare_numerator_eq_zero hPoincare
  · simpa only [D0] using hGradient
  · simpa only [T, scratch_cmp85SourceGeneratedPrefixTower] using hQnext

/-- Literal counting-Hilbert presentation of the positive-level coarse
precision in CMP85 (2.30).  `Qstep` is the one-step averaging operator, not
the fine-carrier prefix operator `Q`.  `cStepCount` is the coefficient after
converting the printed one-step weighted adjoint to Lean's counting adjoint;
it is not definitionally the printed `cStepWeighted`. -/
noncomputable def scratch_cmp85CoarsePrecision
    {H F C : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    (Q : H →L[ℝ] F) (G : H →L[ℝ] H) (Qstep : F →L[ℝ] C)
    (bWeighted bCount cStepCount : ℝ) : F →L[ℝ] F :=
  scratch_cmp85EffectiveQuadratic Q G bWeighted bCount +
    cStepCount • (Qstep.adjoint.comp Qstep)

/-- The quadratic form of the literal coarse precision is exactly the P2b
completed square plus the one-step projector square. -/
theorem scratch_inner_cmp85CoarsePrecision_eq_completedSquare
    {H F C : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (Qstep : F →L[ℝ] C)
    {bWeighted bCount cStepCount : ℝ} (hbCount : bCount ≠ 0)
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (eta : F) :
    let phi := scratch_cmp85SchurFineField Q G bCount eta
    inner ℝ eta
        (scratch_cmp85CoarsePrecision Q G Qstep
          bWeighted bCount cStepCount eta) =
      (bWeighted / bCount) * inner ℝ phi (D phi) +
        bWeighted * ‖eta - Q phi‖ ^ 2 +
        cStepCount * ‖Qstep eta‖ ^ 2 := by
  dsimp only
  rw [scratch_cmp85CoarsePrecision,
    ContinuousLinearMap.add_apply, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq,
    scratch_inner_cmp85EffectiveQuadratic_eq_completedSquare
      D Q G hbCount hKG eta]

/-- Kernel elimination for the literal coarse precision.  The final
`hZeroControl` premise is deliberately phrased as a zero-energy statement;
the physical P2c producer must prove it from the prefix-`j+1` Poincare
inequality and the tower recursion. -/
theorem scratch_cmp85CoarsePrecision_eq_zero_imp
    {H F C : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (Qstep : F →L[ℝ] C)
    {bWeighted bCount cStepCount : ℝ}
    (hbWeighted : 0 < bWeighted) (hbCount : 0 < bCount)
    (hcStepCount : 0 < cStepCount)
    (hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi))
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (hZeroControl : ∀ phi,
      inner ℝ phi (D phi) = 0 → Qstep (Q phi) = 0 → phi = 0)
    {eta : F}
    (heta : scratch_cmp85CoarsePrecision Q G Qstep
      bWeighted bCount cStepCount eta = 0) :
    eta = 0 := by
  let phi := scratch_cmp85SchurFineField Q G bCount eta
  have hquad := scratch_inner_cmp85CoarsePrecision_eq_completedSquare
    D Q G Qstep hbCount.ne' hKG eta
  rw [heta, inner_zero_right] at hquad
  have hx0 :
      0 ≤ (bWeighted / bCount) * inner ℝ phi (D phi) :=
    mul_nonneg (div_nonneg hbWeighted.le hbCount.le) (hDnonneg phi)
  have hy0 : 0 ≤ bWeighted * ‖eta - Q phi‖ ^ 2 :=
    mul_nonneg hbWeighted.le (sq_nonneg _)
  have hz0 : 0 ≤ cStepCount * ‖Qstep eta‖ ^ 2 :=
    mul_nonneg hcStepCount.le (sq_nonneg _)
  have hx : (bWeighted / bCount) * inner ℝ phi (D phi) = 0 := by
    nlinarith
  have hy : bWeighted * ‖eta - Q phi‖ ^ 2 = 0 := by
    nlinarith
  have hz : cStepCount * ‖Qstep eta‖ ^ 2 = 0 := by
    nlinarith
  have hEnergy : inner ℝ phi (D phi) = 0 :=
    (mul_eq_zero.mp hx).resolve_left (div_ne_zero hbWeighted.ne' hbCount.ne')
  have hMismatchSq : ‖eta - Q phi‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hy).resolve_left hbWeighted.ne'
  have hStepSq : ‖Qstep eta‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left hcStepCount.ne'
  have hEta : eta = Q phi := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hMismatchSq))
  have hStep : Qstep eta = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hStepSq)
  have hPhi : phi = 0 := by
    apply hZeroControl phi hEnergy
    simpa only [hEta] using hStep
  rw [hEta, hPhi, map_zero]

/-- The literal positive-level coarse precision is injective once the
prefix-Poincare zero-control implication has been discharged. -/
theorem scratch_cmp85CoarsePrecision_injective
    {H F C : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
    (D : H →L[ℝ] H) (Q : H →L[ℝ] F) (G : H →L[ℝ] H)
    (Qstep : F →L[ℝ] C)
    {bWeighted bCount cStepCount : ℝ}
    (hbWeighted : 0 < bWeighted) (hbCount : 0 < bCount)
    (hcStepCount : 0 < cStepCount)
    (hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi))
    (hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ H)
    (hZeroControl : ∀ phi,
      inner ℝ phi (D phi) = 0 → Qstep (Q phi) = 0 → phi = 0) :
    Function.Injective
      (scratch_cmp85CoarsePrecision Q G Qstep
        bWeighted bCount cStepCount) := by
  intro eta zeta hEq
  apply sub_eq_zero.mp
  apply scratch_cmp85CoarsePrecision_eq_zero_imp
    D Q G Qstep hbWeighted hbCount hcStepCount hDnonneg hKG hZeroControl
  rw [map_sub, hEq, sub_self]

/-- Finite-dimensional inverse of an injective continuous endomorphism.
This generic helper may accept injectivity; the source-facing P2c producer
must construct the preceding theorem internally. -/
noncomputable def scratch_inverseOfInjectiveCLM
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : F →L[ℝ] F) (hA : Function.Injective A) : F →L[ℝ] F :=
  ((A.toLinearMap.linearEquivOfInjective
    (by
      intro x y hxy
      exact hA hxy)
    rfl).toContinuousLinearEquiv).symm.toContinuousLinearMap

theorem scratch_inverseOfInjectiveCLM_comp
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : F →L[ℝ] F) (hA : Function.Injective A) :
    (scratch_inverseOfInjectiveCLM A hA).comp A =
      ContinuousLinearMap.id ℝ F := by
  ext x
  exact ((A.toLinearMap.linearEquivOfInjective
    (by
      intro u v huv
      exact hA huv)
    rfl).toContinuousLinearEquiv).symm_apply_apply x

theorem scratch_comp_inverseOfInjectiveCLM
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : F →L[ℝ] F) (hA : Function.Injective A) :
    A.comp (scratch_inverseOfInjectiveCLM A hA) =
      ContinuousLinearMap.id ℝ F := by
  ext x
  exact ((A.toLinearMap.linearEquivOfInjective
    (by
      intro u v huv
      exact hA huv)
    rfl).toContinuousLinearEquiv).apply_symm_apply x

/-! ## Source-facing P2c package -/

/-- A positive source prefix that still has a literal next averaging step. -/
abbrev ScratchCMP85PositiveCoarseStep (depth : ℕ) :=
  {k : Fin depth // 0 < k.val}

/-- The current positive prefix corresponding to a positive coarse step. -/
def ScratchCMP85PositiveCoarseStep.currentPrefix
    {depth : ℕ} (k : ScratchCMP85PositiveCoarseStep depth) :
    ScratchCMP85PositivePrefix depth :=
  ⟨k.1.castSucc, k.2⟩

/-- Literal generated positive-level precision of CMP85 (2.30), in the
counting-Hilbert presentation. -/
noncomputable def scratch_cmp85SourceGeneratedCoarsePrecision
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
    (k : ScratchCMP85PositiveCoarseStep depth) :=
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  scratch_cmp85CoarsePrecision (T.towerAt r.1).Qprime
    (scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall r)
    (T.nextAverage k.1)
    (scratch_cmp85SourcePrefixWeightedCoefficient T a r)
    (scratch_cmp85SourcePrefixCountingCoefficient T a r)
    (scratch_cmp85SourceStepCountingCoefficient T a k.1)

/-- The generated counting precision is exactly the two weighted-adjoint
terms printed in CMP85 (2.21)+(2.30).  Both normalization dictionaries are
cited explicitly. -/
theorem scratch_cmp85SourceGeneratedCoarsePrecision_eq_weighted
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
    (k : ScratchCMP85PositiveCoarseStep depth) :
    let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r := k.currentPrefix
    let Q := (T.towerAt r.1).Qprime
    let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    let bWeighted := scratch_cmp85SourcePrefixWeightedCoefficient T a r
    let cStepWeighted := scratch_cmp85SourceStepWeightedCoefficient T a k.1
    scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k =
      (bWeighted • ContinuousLinearMap.id ℝ
          (T.towerAt r.1).TerminalSpace.carrier -
        bWeighted ^ 2 •
          (Q.comp (G.comp (T.towerAt r.1).weightedAdjoint))) +
        cStepWeighted •
          ((scratch_cmp85SourceStepWeightedAdjoint T k.1).comp
            (T.nextAverage k.1)) := by
  dsimp only
  unfold scratch_cmp85SourceGeneratedCoarsePrecision
  unfold scratch_cmp85CoarsePrecision
  rw [← scratch_cmp85SourceEffectiveQuadratic_weighted_eq_counting
    T G hspacing r]
  rw [← scratch_cmp85SourceStepWeightedTerm_eq_counting T a k.1]

/-- The source-generated coarse precision is injective.  The proof constructs
the next-prefix zero control internally; no positivity or inverse of the
coarse precision is accepted. -/
theorem scratch_cmp85SourceGeneratedCoarsePrecision_injective
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
    (k : ScratchCMP85PositiveCoarseStep depth) :
    Function.Injective
      (scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k) := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let D := scratch_cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let Q := (T.towerAt r.1).Qprime
  let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  let Qstep := T.nextAverage k.1
  let bWeighted := scratch_cmp85SourcePrefixWeightedCoefficient T a r
  let bCount := scratch_cmp85SourcePrefixCountingCoefficient T a r
  let cStepCount := scratch_cmp85SourceStepCountingCoefficient T a k.1
  have hbWeighted : 0 < bWeighted :=
    scratch_cmp85SourcePrefixWeightedCoefficient_pos T ha hspacing r
  have hbCount : 0 < bCount :=
    scratch_cmp85SourcePrefixCountingCoefficient_pos T ha hspacing r
  have hcStepCount : 0 < cStepCount :=
    scratch_cmp85SourceStepCountingCoefficient_pos T ha hspacing k.1
  have hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi) := by
    intro phi
    rw [D, scratch_inner_cmp85BareMassPrecision,
      inner_cmp99ActiveRegionSourceCovariantLaplacian]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖))
  have hKG : (cmp99SourceGaugePrecision D Q bCount).comp G =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [D, Q, G, bCount, T, r,
      scratch_cmp85SourceGeneratedPrefixPrecision,
      scratch_cmp85SourceGeneratedPrefixTower] using
      scratch_cmp85SourceGeneratedPrefixPrecision_comp_green hd hM Omega0
        depth hspacing ha mass background0 chain fineSmall hsmall r
  have hZeroControl : ∀ phi,
      inner ℝ phi (D phi) = 0 → Qstep (Q phi) = 0 → phi = 0 := by
    intro phi hEnergy hStep
    exact scratch_cmp85SourceGeneratedPrefix_zeroControl hd hM Omega0 depth
      hspacing mass background0 chain fineSmall hsmall k.1 phi hEnergy hStep
  change Function.Injective
    (scratch_cmp85CoarsePrecision Q G Qstep
      bWeighted bCount cStepCount)
  exact scratch_cmp85CoarsePrecision_injective D Q G Qstep
    hbWeighted hbCount hcStepCount hDnonneg hKG hZeroControl

/-- CMP85's positive-level coarse covariance `C^(j)`, constructed as the
finite-dimensional inverse of the literal (2.30) precision. -/
noncomputable def scratch_cmp85SourceGeneratedCoarseCovariance
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
    (k : ScratchCMP85PositiveCoarseStep depth) :=
  scratch_inverseOfInjectiveCLM
    (scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k)
    (scratch_cmp85SourceGeneratedCoarsePrecision_injective hd hM Omega0
      depth hspacing ha mass background0 chain fineSmall hsmall k)

theorem scratch_cmp85SourceGeneratedCoarseCovariance_comp_precision
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
    (k : ScratchCMP85PositiveCoarseStep depth) :
    (scratch_cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k).comp
      (scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k) =
      ContinuousLinearMap.id ℝ _ := by
  exact scratch_inverseOfInjectiveCLM_comp _ _

theorem scratch_cmp85SourceGeneratedCoarsePrecision_comp_covariance
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
    (k : ScratchCMP85PositiveCoarseStep depth) :
    (scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k).comp
      (scratch_cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k) =
      ContinuousLinearMap.id ℝ _ := by
  exact scratch_comp_inverseOfInjectiveCLM _ _

end

end YangMills.RG
