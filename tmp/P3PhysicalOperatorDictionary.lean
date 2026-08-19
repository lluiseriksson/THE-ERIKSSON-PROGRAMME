import tmp.P3PhysicalScalarSpecialization

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only physical operator dictionary for P3.

The three equalities in this file identify the typed generic objects with
the independently generated P2a/P2c objects.  No precision, Green operator,
or inverse law is supplied by the caller.  This file is not compiler
evidence and is not imported by the tracked tree.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The typed fine precision in source-weighted orientation is exactly the
generated P2a prefix precision in counting coordinates. -/
theorem scratch_cmp85SourceGeneratedPrefixPrecision_eq_typed
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
    (r : ScratchCMP85PositivePrefix depth) :
    let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let D := scratch_cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    scratch_cmp85TypedFinePrecision D (T.towerAt r.1).Qprime
        (T.towerAt r.1).weightedAdjoint
        (scratch_cmp85SourcePrefixWeightedCoefficient T a r) =
      scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall r := by
  dsimp only
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let D := scratch_cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  have hweighted := scratch_cmp85SourcePrefixPrecision_weighted_eq_counting
    T D (a := a) hspacing r
  simpa only [scratch_cmp85TypedFinePrecision,
    scratch_cmp85SourceGeneratedPrefixPrecision, T, D,
    scratch_cmp85SourceGeneratedPrefixTower] using hweighted

/-- The typed Schur precision is exactly the independently generated P2c
coarse precision, with both weighted/counting dictionaries already cited. -/
theorem scratch_cmp85SourceGeneratedCoarsePrecision_eq_typed
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
    let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
      hspacing ha mass background0 chain fineSmall hsmall r
    scratch_cmp85SourceGeneratedCoarsePrecision hd hM Omega0 depth
        hspacing ha mass background0 chain fineSmall hsmall k =
      scratch_cmp85TypedSchurPrecision
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (scratch_cmp85SourceStepWeightedAdjoint T k.1)
        G (scratch_cmp85SourcePrefixWeightedCoefficient T a r)
        (scratch_cmp85SourceStepWeightedCoefficient T a k.1) := by
  dsimp only
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let G := scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth
    hspacing ha mass background0 chain fineSmall hsmall r
  have hweighted := scratch_cmp85SourceGeneratedCoarsePrecision_eq_weighted
    hd hM Omega0 depth hspacing ha mass background0 chain fineSmall hsmall k
  simpa only [scratch_cmp85TypedSchurPrecision,
    scratch_cmp85TypedGreenSandwich, scratch_cmp85TypedStepProjector,
    T, r, G] using hweighted

/-- The typed next precision is the generated P2a precision of the next
positive prefix.  This is where the recursion of `Q'`, the weighted-adjoint
factorization, and the source index shift meet. -/
theorem scratch_cmp85SourceGeneratedNextPrefixPrecision_eq_typed
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
    (k : ScratchCMP85PositiveCoarseStep depth) :
    let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
      spacing epsilon background0 chain fineSmall
    let r := k.currentPrefix
    let rn := k.nextPrefix
    let D := scratch_cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass
    let beta := scratch_cmp85RecurrenceBeta a (M : ℝ)
      (T.towerAt r.1).terminalSpacing (k.1.val - 1)
    scratch_cmp85TypedNextPrecision D
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (scratch_cmp85SourceStepWeightedAdjoint T k.1)
        beta =
      scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall rn := by
  dsimp only
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let r := k.currentPrefix
  let rn := k.nextPrefix
  let D := scratch_cmp85BareMassPrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
      (matrixSUNAdjointModel Nc) background0 spacing)
    mass
  let beta := scratch_cmp85RecurrenceBeta a (M : ℝ)
    (T.towerAt r.1).terminalSpacing (k.1.val - 1)
  have hQ := T.Qprime_succ k.1
  have hbeta := scratch_cmp85RecurrenceBeta_eq_sourceNextWeighted T a k
  have hweighted := scratch_cmp85SourcePrefixPrecision_weighted_eq_counting
    T D (a := a) hspacing rn
  calc
    scratch_cmp85TypedNextPrecision D
        (T.towerAt r.1).Qprime (T.towerAt r.1).weightedAdjoint
        (T.nextAverage k.1) (scratch_cmp85SourceStepWeightedAdjoint T k.1)
        beta =
      D + beta •
        ((T.towerAt r.1).weightedAdjoint.comp
          (scratch_cmp85SourceStepWeightedAdjoint T k.1)).comp
        ((T.nextAverage k.1).comp (T.towerAt r.1).Qprime) := by
          rfl
    _ = D + scratch_cmp85SourcePrefixWeightedCoefficient T a rn •
        ((T.towerAt rn.1).weightedAdjoint.comp
          (T.towerAt rn.1).Qprime) := by
          dsimp [beta]
          rw [hbeta]
          dsimp [r, rn]
          congr 1
          apply ContinuousLinearMap.ext
          intro eta
          rw [hQ]
          exact (scratch_cmp85SourceWeightedAdjoint_succ
            T hspacing k.1
              ((T.nextAverage k.1) ((T.towerAt r.1).Qprime eta))).symm
    _ = scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall rn := by
          simpa only [scratch_cmp85SourceGeneratedPrefixPrecision,
            T, rn, D, scratch_cmp85SourceGeneratedPrefixTower] using hweighted

end

end YangMills.RG
