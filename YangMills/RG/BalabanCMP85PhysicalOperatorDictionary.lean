import YangMills.RG.BalabanCMP85PhysicalScalarSpecialization
/-!
physical operator dictionary for P3.

The three equalities in this file identify the typed generic objects with the independently generated P2a/P2c objects. No precision, Green operator, or inverse law is supplied by the caller.

-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The typed fine precision in source-weighted orientation is exactly the
generated P2a prefix precision in counting coordinates. -/
theorem cmp85SourceGeneratedPrefixPrecision_eq_typed
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : CMP85PositivePrefix depth) :
    let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let D := cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    cmp85TypedFinePrecision D (T.towerAt r.1).Qprime
        (T.towerAt r.1).weightedAdjoint
        (cmp85SourcePrefixWeightedCoefficient T a r) =
      cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall r := by
  dsimp only
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let D := cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  have hweighted := cmp85SourcePrefixPrecision_weighted_eq_counting
    T D (a := a) hspacing r
  simpa only [cmp85TypedFinePrecision,
    cmp85SourceGeneratedPrefixPrecision, T, D,
    cmp85SourceGeneratedPrefixTower] using hweighted

/-- The typed Schur precision is exactly the independently generated P2c
coarse precision, with both weighted/counting dictionaries already cited. -/
theorem cmp85SourceGeneratedCoarsePrecision_eq_typed
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
    let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k =
      cmp85TypedSchurPrecision
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (cmp85SourceStepWeightedAdjoint T k.1)
        G (cmp85SourcePrefixWeightedCoefficient T a r)
        (cmp85SourceStepWeightedCoefficient T a k.1) := by
  dsimp only
  let T := cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let G := cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  have hweighted := cmp85SourceGeneratedCoarsePrecision_eq_weighted
    hd hM Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  simpa only [cmp85TypedSchurPrecision,
    cmp85TypedGreenSandwich, cmp85TypedStepProjector,
    T, r, G] using hweighted

/-- The typed next precision is the generated P2a precision of the next
positive prefix.  This is where the recursion of `Q'`, the weighted-adjoint
factorization, and the source index shift meet. -/
theorem cmp85SourceGeneratedNextPrefixPrecision_eq_typed
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
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
    let beta := cmp85RecurrenceBeta a (M : ℝ)
      (T.towerAt r.1).terminalSpacing (k.1.val - 1)
    cmp85TypedNextPrecision D
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (cmp85SourceStepWeightedAdjoint T k.1)
        beta =
      cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall rn := by
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
  let beta := cmp85RecurrenceBeta a (M : ℝ)
    (T.towerAt r.1).terminalSpacing (k.1.val - 1)
  have hQ := T.Qprime_succ k.1
  have hbeta := cmp85RecurrenceBeta_eq_sourceNextWeighted T a k
  have hweighted := cmp85SourcePrefixPrecision_weighted_eq_counting
    T D (a := a) hspacing rn
  calc
    cmp85TypedNextPrecision D
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (cmp85SourceStepWeightedAdjoint T k.1)
        beta =
      D + beta •
        ((T.towerAt r.1).weightedAdjoint.comp
          (cmp85SourceStepWeightedAdjoint T k.1)).comp
        ((T.nextAverage k.1).comp (T.towerAt r.1).Qprime) := by
          rfl
    _ = D + cmp85SourcePrefixWeightedCoefficient T a rn •
        ((T.towerAt rn.1).weightedAdjoint.comp
          (T.towerAt rn.1).Qprime) := by
          dsimp [beta]
          rw [hbeta]
          dsimp [r, rn]
          congr 1
          apply ContinuousLinearMap.ext
          intro eta
          have hQeta := congrArg (fun Q => Q eta) hQ
          simp only [ContinuousLinearMap.comp_apply] at hQeta
          have hQeta' :
              (T.towerAt rn.1).Qprime eta =
                (T.nextAverage k.1) ((T.towerAt r.1).Qprime eta) := by
            simpa [r, rn] using hQeta
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.smul_apply]
          rw [hQeta']
          exact congrArg
            (fun z =>
              cmp85SourcePrefixWeightedCoefficient T a rn • z)
            (cmp85SourceWeightedAdjoint_succ
              T hspacing k.1
                ((T.nextAverage k.1) ((T.towerAt r.1).Qprime eta))).symm
    _ = cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall rn := by
          simpa only [cmp85SourceGeneratedPrefixPrecision,
            T, rn, D, cmp85SourceGeneratedPrefixTower] using hweighted

end

end YangMills.RG
