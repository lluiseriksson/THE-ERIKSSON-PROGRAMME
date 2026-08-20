import YangMills.RG.BalabanCMP85Eq241Eq242PhysicalGreenRecurrence
/-!
source-complete base identity `G_1 = C^(0)` from CMP85.

`C^(0)` is constructed independently from the literal base precision. It is not defined to be `G_1`, and P2c is not invoked at index zero.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Literal first retained step. -/
def cmp85FirstStep {depth : ℕ} (hdepth : 0 < depth) : Fin depth :=
  ⟨0, hdepth⟩

/-- Literal source prefix one; the empty prefix is not reinterpreted as the
first physical source scale. -/
def cmp85FirstPositivePrefix {depth : ℕ} (hdepth : 0 < depth) :
    CMP85PositivePrefix depth :=
  ⟨(cmp85FirstStep hdepth).succ, by simp [cmp85FirstStep]⟩

/-- CMP85's literal base precision `(2.17)+(2.30)` on the fine carrier. -/
noncomputable def cmp85BasePrecision
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (D : H →L[ℝ] H) (R : H →L[ℝ] K) (Rdag : K →L[ℝ] H)
    (a spacing1 : ℝ) : H →L[ℝ] H :=
  D + (a * spacing1⁻¹ ^ 2) • Rdag.comp R

/-- At the first retained scale, the total average factors through the
literal one-step average and the empty-prefix average.  No dependent carrier
identification is hidden in this statement. -/
theorem cmp85SourceFirstPrefix_Qprime_eq_step
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hdepth : 0 < depth) :
    (T.towerAt (cmp85FirstPositivePrefix hdepth).1).Qprime =
      (T.nextAverage (cmp85FirstStep hdepth)).comp
        (T.towerAt (cmp85FirstStep hdepth).castSucc).Qprime := by
  simpa only [cmp85FirstPositivePrefix, cmp85FirstStep] using
    T.Qprime_succ (cmp85FirstStep hdepth)

/-- The first prefix weighted adjoint factors through the empty-prefix
weighted adjoint and the literal one-step weighted adjoint, with the exact
`M^d` volume normalization. -/
theorem cmp85SourceFirstPrefix_weightedAdjoint_eq_step
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hspacing : 0 < spacing) (hdepth : 0 < depth) :
    (T.towerAt (cmp85FirstPositivePrefix hdepth).1).weightedAdjoint =
      (T.towerAt (cmp85FirstStep hdepth).castSucc).weightedAdjoint.comp
        (cmp85SourceStepWeightedAdjoint T
          (cmp85FirstStep hdepth)) := by
  apply ContinuousLinearMap.ext
  intro eta
  simpa only [cmp85FirstPositivePrefix, cmp85FirstStep,
    ContinuousLinearMap.comp_apply] using
      cmp85SourceWeightedAdjoint_succ T hspacing
        (cmp85FirstStep hdepth) eta

/-- At source prefix one, `a_1=a`; the coefficient is exactly the literal
base coefficient. -/
theorem cmp85SourceFirstPrefixWeightedCoefficient_eq
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)} {depth : ℕ}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (a : ℝ) (hdepth : 0 < depth) :
    cmp85SourcePrefixWeightedCoefficient T a
        (cmp85FirstPositivePrefix hdepth) =
      a * (T.towerAt (cmp85FirstPositivePrefix hdepth).1).terminalSpacing⁻¹ ^ 2 := by
  unfold cmp85SourcePrefixWeightedCoefficient
  unfold cmp85SourcePrefixA
  have hindex :
      (cmp85FirstPositivePrefix hdepth).1.val - 1 = 0 := by
    simp [cmp85FirstPositivePrefix, cmp85FirstStep]
  rw [hindex, cmp99SourceMassParameter_zero]

/-- The separately written literal base precision equals the generated P2a
precision at source prefix one. -/
theorem cmp85SourceGeneratedBasePrecision_eq_prefixOne
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r1 := cmp85FirstPositivePrefix hdepth
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    cmp85BasePrecision D
        (T.towerAt r1.1).Qprime
        (T.towerAt r1.1).weightedAdjoint
        a (T.towerAt r1.1).terminalSpacing =
      cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall r1 := by
  dsimp only
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r1 := cmp85FirstPositivePrefix hdepth
  let D := cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  have hb := cmp85SourceFirstPrefixWeightedCoefficient_eq T a hdepth
  have hweighted := cmp85SourcePrefixPrecision_weighted_eq_counting
    (a := a) T D hspacing r1
  rw [hb] at hweighted
  simpa only [cmp85BasePrecision,
    cmp85SourceGeneratedPrefixPrecision,
    T, r1, D, cmp85SourceGeneratedPrefixTower] using hweighted

/-- Coercivity of the separately written base precision, transported only
after its literal equality with P2a has been proved. -/
theorem isCoerciveCLM_cmp85SourceGeneratedBasePrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r1 := cmp85FirstPositivePrefix hdepth
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    IsCoerciveCLM
      (cmp85BasePrecision D
        (T.towerAt r1.1).Qprime
        (T.towerAt r1.1).weightedAdjoint
        a (T.towerAt r1.1).terminalSpacing)
      (cmp85SourceGeneratedPrefixCoercivity hd hM Omega0 depth
        spacing epsilon a background0 chain fineSmall r1) := by
  dsimp only
  rw [cmp85SourceGeneratedBasePrecision_eq_prefixOne hd hM Omega0
    depth hdepth hspacing mass background0 chain fineSmall]
  exact isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision hd hM
    Omega0 depth hspacing ha mass background0 chain fineSmall hsmall
      (cmp85FirstPositivePrefix hdepth)

/-- Independently generated `C^(0)`, obtained by inverting the literal base
precision rather than aliasing `G_1`. -/
noncomputable def cmp85SourceGeneratedBaseCovariance
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :=
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r1 := cmp85FirstPositivePrefix hdepth
  let D := cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let K0 := cmp85BasePrecision D
    (T.towerAt r1.1).Qprime
    (T.towerAt r1.1).weightedAdjoint
    a (T.towerAt r1.1).terminalSpacing
  covarianceOfIsCoerciveCLM K0
    (cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall r1)
    (isCoerciveCLM_cmp85SourceGeneratedBasePrecision hd hM Omega0
      depth hdepth hspacing ha mass background0 chain fineSmall hsmall)

theorem cmp85SourceGeneratedBasePrecision_comp_covariance
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r1 := cmp85FirstPositivePrefix hdepth
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    (cmp85BasePrecision D
      (T.towerAt r1.1).Qprime
      (T.towerAt r1.1).weightedAdjoint
      a (T.towerAt r1.1).terminalSpacing).comp
        (cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth
          hdepth hspacing ha mass background0 chain fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  dsimp only
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall
        (cmp85FirstPositivePrefix hdepth)) _

theorem cmp85SourceGeneratedBaseCovariance_comp_precision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r1 := cmp85FirstPositivePrefix hdepth
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    (cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
      hspacing ha mass background0 chain fineSmall hsmall).comp
        (cmp85BasePrecision D
          (T.towerAt r1.1).Qprime
          (T.towerAt r1.1).weightedAdjoint
          a (T.towerAt r1.1).terminalSpacing) =
      ContinuousLinearMap.id ℝ _ := by
  dsimp only
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall
        (cmp85FirstPositivePrefix hdepth)) _

/-- CMP85's base identity `G_1=C^(0)`, proved by uniqueness of right
inverses of the same literal coercive precision. -/
theorem cmp85SourceGeneratedPrefixGreen_one_eq_baseCovariance
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ) (hdepth : 0 < depth)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1) :
    cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall
        (cmp85FirstPositivePrefix hdepth) =
      cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
        hspacing ha mass background0 chain fineSmall hsmall := by
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r1 := cmp85FirstPositivePrefix hdepth
  let D := cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let K0 := cmp85BasePrecision D
    (T.towerAt r1.1).Qprime
    (T.towerAt r1.1).weightedAdjoint
    a (T.towerAt r1.1).terminalSpacing
  have hK0 := isCoerciveCLM_cmp85SourceGeneratedBasePrecision hd hM
    Omega0 depth hdepth hspacing ha mass background0 chain fineSmall hsmall
  have hc0 := cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0
    depth hspacing ha background0 chain fineSmall hsmall r1
  have hEq := cmp85SourceGeneratedBasePrecision_eq_prefixOne
    (a := a) hd hM Omega0 depth hdepth hspacing mass background0 chain fineSmall
  have hGRight : K0.comp
      (cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall r1) =
        ContinuousLinearMap.id ℝ _ := by
    dsimp only [K0]
    rw [hEq]
    exact cmp85SourceGeneratedPrefixPrecision_comp_green hd hM
      Omega0 depth hspacing ha mass background0 chain fineSmall hsmall r1
  have hC0Right : K0.comp
      (cmp85SourceGeneratedBaseCovariance hd hM Omega0 depth hdepth
        hspacing ha mass background0 chain fineSmall hsmall) =
        ContinuousLinearMap.id ℝ _ := by
    exact cmp85SourceGeneratedBasePrecision_comp_covariance hd hM
      Omega0 depth hdepth hspacing ha mass background0 chain fineSmall hsmall
  apply ContinuousLinearMap.ext
  intro x
  apply isCoerciveCLM_injective K0 hc0 hK0
  have hGRight_x := congrArg (fun T : _ →L[ℝ] _ => T x) hGRight
  have hC0Right_x := congrArg (fun T : _ →L[ℝ] _ => T x) hC0Right
  simpa using hGRight_x.trans hC0Right_x.symm

end

end YangMills.RG
