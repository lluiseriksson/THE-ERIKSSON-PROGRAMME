import YangMills.RG.BalabanCMP85PhysicalOperatorDictionary
/-!
source-complete producer for CMP85 (2.41)--(2.42).

Every operator in the two conclusions is generated internally from the single retained tower. The only public analytic/scalar inputs are those already required by P2a/P2c.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Source-generated typed pair underlying (2.42) and (2.41).  Returning the
two equalities together prevents the averaged recurrence from being replaced
by a later orientation convention. -/
theorem cmp85SourceGeneratedGreenRecurrence_typed
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
    (k : CMP85PositiveCoarseStep depth) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r := k.currentPrefix
    let rn := k.nextPrefix
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    let Q := (T.towerAt r.1).Qprime
    let Qdag := (T.towerAt r.1).weightedAdjoint
    let R := T.nextAverage k.1
    let Rdag := cmp85SourceStepWeightedAdjoint T k.1
    let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    let Gnext := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall rn
    let C := cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k
    let b := cmp85SourcePrefixWeightedCoefficient T a r
    let c := cmp85SourceStepWeightedCoefficient T a k.1
    let beta := cmp85SourcePrefixWeightedCoefficient T a rn
    Gnext = cmp85TypedGreenCandidate Q Qdag G C b ∧
      R.comp (Q.comp Gnext) =
        (b + c) • R.comp (C.comp (Q.comp G)) := by
  dsimp only
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let rn := k.nextPrefix
  let D := cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let Q := (T.towerAt r.1).Qprime
  let Qdag := (T.towerAt r.1).weightedAdjoint
  let R := T.nextAverage k.1
  let Rdag := cmp85SourceStepWeightedAdjoint T k.1
  let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  let Gnext := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall rn
  let C := cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall k
  let b := cmp85SourcePrefixWeightedCoefficient T a r
  let c := cmp85SourceStepWeightedCoefficient T a k.1
  let beta := cmp85SourcePrefixWeightedCoefficient T a rn
  have hcoiso : R.comp Rdag = ContinuousLinearMap.id ℝ
      (T.towerAt k.1.succ).TerminalSpace.carrier := by
    exact cmp85SourceStep_comp_weightedAdjoint T hspacing k.1
  have hFineDict := cmp85SourceGeneratedPrefixPrecision_eq_typed
    (a := a) hd hM Omega0 depth hspacing mass background0 chain fineSmall r
  have hFineRight :
      (cmp85TypedFinePrecision D Q Qdag b).comp G =
        ContinuousLinearMap.id ℝ _ := by
    rw [hFineDict]
    exact cmp85SourceGeneratedPrefixPrecision_comp_green hd hM
      Omega0 depth hspacing ha mass background0 chain fineSmall hsmall r
  have hCoarseDict := cmp85SourceGeneratedCoarsePrecision_eq_typed
    hd hM Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  have hCRight :
      (cmp85TypedSchurPrecision Q Qdag R Rdag G b c).comp C =
        ContinuousLinearMap.id ℝ _ := by
    rw [← hCoarseDict]
    exact cmp85SourceGeneratedCoarsePrecision_comp_covariance hd hM
      Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  have hNextDict0 :=
    cmp85SourceGeneratedNextPrefixPrecision_eq_typed (a := a) hd hM Omega0
      depth hspacing mass background0 chain fineSmall k
  have hbeta := cmp85RecurrenceBeta_eq_sourceNextWeighted T a k
  have hNextDict :
      cmp85TypedNextPrecision D Q Qdag R Rdag beta =
        cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
          spacing epsilon mass a background0 chain fineSmall rn := by
    simpa only [T, r, rn, D, Q, Qdag, R, Rdag, beta, hbeta] using hNextDict0
  have hNextLeft :
      Gnext.comp (cmp85TypedNextPrecision D Q Qdag R Rdag beta) =
        ContinuousLinearMap.id ℝ _ := by
    rw [hNextDict]
    exact cmp85SourceGeneratedPrefixGreen_comp_precision hd hM
      Omega0 depth hspacing ha mass background0 chain fineSmall hsmall rn
  have hb := cmp85RecurrenceB_eq_sourceCurrentWeighted T a k
  have hc := cmp85RecurrenceC_eq_sourceStepWeighted T a k
  have hcurrentSpacing : 0 < (T.towerAt r.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos
      (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val) hspacing
  have hrec0 := cmp85RecurrenceBeta_mul_add_eq_mul
    (a := a) (L := (M : ℝ))
    (spacingJ := (T.towerAt r.1).terminalSpacing)
    ha (by exact_mod_cast (NeZero.pos M)) hcurrentSpacing (k.1.val - 1)
  have hrec : beta * (b + c) = b * c := by
    simpa only [T, r, rn, b, c, beta, hb, hc, hbeta] using hrec0
  constructor
  · exact cmp85TypedGreen_eq_candidate D Q Qdag R Rdag G Gnext C
      b c beta hcoiso hFineRight hCRight hNextLeft hrec
  · exact cmp85Typed_averagedGreenRecurrence D Q Qdag R Rdag
      G Gnext C b c beta hcoiso hFineRight hCRight hNextLeft hrec

/-- Literal source form of CMP85 (2.42). -/
theorem cmp85SourceGeneratedGreenRecurrence_eq242
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
    (k : CMP85PositiveCoarseStep depth) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r := k.currentPrefix
    let rn := k.nextPrefix
    let Q := (T.towerAt r.1).Qprime
    let Qdag := (T.towerAt r.1).weightedAdjoint
    let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    let Gnext := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall rn
    let C := cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k
    Gnext = G +
      ((cmp85SourcePrefixA (M := M) a r) ^ 2 *
          (T.towerAt r.1).terminalSpacing⁻¹ ^ 4) •
        G.comp (Qdag.comp (C.comp (Q.comp G))) := by
  dsimp only
  have hpair := cmp85SourceGeneratedGreenRecurrence_typed hd hM
    Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  have hEq := hpair.1
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  have hb := cmp85RecurrenceB_eq_sourceCurrentWeighted T a k
  have hb2 := cmp85RecurrenceB_sq a (M : ℝ)
    (T.towerAt r.1).terminalSpacing (k.1.val - 1)
  rw [hb] at hb2
  simp only [cmp85TypedGreenCandidate] at hEq
  rw [hb2] at hEq
  simpa only [r, cmp85SourcePrefixA] using hEq

/-- Literal source form of CMP85 (2.41). -/
theorem cmp85SourceGeneratedGreenRecurrence_eq241
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
    (k : CMP85PositiveCoarseStep depth) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r := k.currentPrefix
    let rn := k.nextPrefix
    let Q := (T.towerAt r.1).Qprime
    let R := T.nextAverage k.1
    let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    let Gnext := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall rn
    let C := cmp85SourceGeneratedCoarseCovariance hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall k
    (T.towerAt rn.1).Qprime.comp Gnext =
      ((a * cmp85SourcePrefixA (M := M) a r /
          cmp85SourcePrefixA (M := M) a rn) *
          (T.towerAt r.1).terminalSpacing⁻¹ ^ 2) •
        R.comp (C.comp (Q.comp G)) := by
  dsimp only
  have hpair := cmp85SourceGeneratedGreenRecurrence_typed hd hM
    Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  have hAvg := hpair.2
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let rn := k.nextPrefix
  let Gnext := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall rn
  have hQ := T.Qprime_succ k.1
  have hb := cmp85RecurrenceB_eq_sourceCurrentWeighted T a k
  have hc := cmp85RecurrenceC_eq_sourceStepWeighted T a k
  have hcurrentSpacing : 0 < (T.towerAt r.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos
      (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val) hspacing
  have hsum := cmp85Recurrence_add_eq_eq241Coefficient
    (a := a) (L := (M : ℝ))
    (spacingJ := (T.towerAt r.1).terminalSpacing)
    ha (by exact_mod_cast (NeZero.pos M)) hcurrentSpacing (k.1.val - 1)
  rw [hb, hc] at hsum
  have hk : k.1.val - 1 + 1 = k.1.val := by
    omega
  have hsum' :
      cmp85SourcePrefixWeightedCoefficient T a r +
          cmp85SourceStepWeightedCoefficient T a k.1 =
        (a * cmp85SourcePrefixA (M := M) a r /
            cmp85SourcePrefixA (M := M) a rn) *
          (T.towerAt r.1).terminalSpacing⁻¹ ^ 2 := by
    simpa [r, rn, cmp85SourcePrefixA,
      CMP85PositiveCoarseStep.currentPrefix,
      CMP85PositiveCoarseStep.nextPrefix, hk] using hsum
  change (T.towerAt k.1.succ).Qprime.comp Gnext = _
  rw [hQ]
  simpa only [T, r, rn, Gnext, ContinuousLinearMap.comp_assoc, hsum'] using hAvg

end

end YangMills.RG
