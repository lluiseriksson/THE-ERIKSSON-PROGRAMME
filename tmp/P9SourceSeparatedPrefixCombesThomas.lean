import tmp.P8SourceSeparatedRegionalPrefixGreen
import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay
import YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

# Per-depth Combes--Thomas bounds for the exact separated prefix

This file uses P7's literal CMP85 final-prefix precision: zero bare mass and
the source counting coefficient generated at prefix `depth`.  The precision
range, norm budget, coercivity and inverse laws are all constructed from the
same physical tower.  P5's ambient Green and P8's local Dirichlet Green then
inherit exponential kernel bounds.

The rate and the displayed Combes--Thomas budget remain visible.  This is a
per-depth statement only: it does not produce uniform CMP99 (3.42) constants,
the four localized source actions, the C6c.4 terminal sup bound, or attainment
of window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The one source-generated coefficient multiplying the final-prefix
`Q'†Q'`.  It includes the counting-Hilbert volume conversion exactly once. -/
noncomputable def scratch_cmp89SourceSeparatedPrefixCountingCoefficient
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) : ℝ :=
  let T := scratch_cmp89SourceSeparatedPrefixTower
    (spacing := spacing) (epsilon := epsilon) hL depth background budget
    fineSmall
  scratch_cmp85SourcePrefixCountingCoefficient T a
    (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))

/-- Exact operator-norm budget for the source prefix: covariant Laplacian
plus the literal CMP85 counting coefficient. -/
noncomputable def scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) : ℝ :=
  16 / spacing ^ 2 +
    |scratch_cmp89SourceSeparatedPrefixCountingCoefficient hL depth
      spacing epsilon a background budget fineSmall|

theorem scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound_pos
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    0 < scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall := by
  unfold scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
  have hbase : 0 < (16 : ℝ) / spacing ^ 2 := by positivity
  linarith [abs_nonneg
    (scratch_cmp89SourceSeparatedPrefixCountingCoefficient hL depth
      spacing epsilon a background budget fineSmall)]

/-- The selected final retained prefix is a contraction in counting norm.
The proof rewrites it to the canonical full weighted tower first. -/
theorem scratch_norm_cmp89SourceSeparatedFinalPrefix_Qprime_le_one
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let T := scratch_cmp89SourceSeparatedPrefixTower
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      (spacing := spacing) (epsilon := epsilon) hL depth background budget
      fineSmall
    ‖(T.towerAt
      (scratch_cmp85LastPositivePrefix (depth + 1)
        (Nat.succ_pos depth)).1).Qprime‖ ≤ 1 := by
  dsimp only
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := L) Omega (depth + 1)
  let T := scratch_cmp89SourceSeparatedPrefixTower
    (spacing := spacing) (epsilon := epsilon) hL depth background budget
    fineSmall
  change ‖(T.towerAt (Fin.last (depth + 1))).Qprime‖ ≤ 1
  have hterminal : T.towerAt (Fin.last (depth + 1)) =
      regions.weightedQprimeTower (by norm_num) hL
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall := by
    simpa only [T, regions, Omega,
      scratch_cmp89SourceSeparatedPrefixTower,
      scratch_cmp85SourceGeneratedPrefixTower] using
      (cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
        (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
        (by norm_num) hL (matrixSUNAdjointModel Nc) Omega
        (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall)
  rw [hterminal]
  exact regions.norm_weightedQprimeTower_Qprime_le_one
    (by norm_num) hL (matrixSUNAdjointModel Nc) hspacing background
    budget.toRadiusChain fineSmall

/-- Elaboration-only name for the exact final-prefix `Q'†Q'`.  Its explicit
ambient endomorphism type prevents the dependent terminal carrier of the
retained tower from leaking into every downstream theorem signature. -/
private noncomputable def scratch_cmp89SourceSeparatedFinalPrefixQprimeMass
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1))
        (SUNLieCoord Nc) :=
  let T := scratch_cmp89SourceSeparatedPrefixTower
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    (spacing := spacing) (epsilon := epsilon) hL depth background budget
    fineSmall
  let r := scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth)
  (T.towerAt r.1).Qprime.adjoint.comp (T.towerAt r.1).Qprime

/-- The exact final-prefix `Q'†Q'` has the printed terminal-block radius. -/
theorem scratch_cmp89SourceSeparatedFinalPrefix_QprimeMass_finiteRange
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpFiniteRange
      (scratch_cmp89SourceSeparatedFinalPrefixQprimeMass
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        hL depth spacing epsilon background budget fineSmall)
      (fun x y : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L)
            (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
            (depth + 1)) =>
        finBoxDist x.1 y.1)
      (L ^ (depth + 1) - 1) := by
  intro source target v hfar
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := L) Omega (depth + 1)
  let T := scratch_cmp89SourceSeparatedPrefixTower
    (spacing := spacing) (epsilon := epsilon) hL depth background budget
    fineSmall
  change (((T.towerAt (Fin.last (depth + 1))).Qprime.adjoint.comp
      (T.towerAt (Fin.last (depth + 1))).Qprime)
        (singleFinitePiLp source v)) target = 0
  have hterminal : T.towerAt (Fin.last (depth + 1)) =
      regions.weightedQprimeTower (by norm_num) hL
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall := by
    simpa only [T, regions, Omega,
      scratch_cmp89SourceSeparatedPrefixTower,
      scratch_cmp85SourceGeneratedPrefixTower] using
      (cmp99SourceGeneratedRetainedPhysicalTower_towerAt_last_eq_weightedQprimeTower
        (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
        (by norm_num) hL (matrixSUNAdjointModel Nc) Omega
        (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall)
  rw [hterminal]
  exact cmp99SourceIteratedLift_QprimeMass_finiteRange
    Omega (depth + 1) (by norm_num) hL (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
      source target v hfar

/-- The complete exact prefix precision has radius `L^(depth+1)`: this
simultaneously dominates the one-link Laplacian and `Q'†Q'` radius. -/
theorem scratch_cmp89SourceSeparatedFinePrefixPrecision_finiteRange
    (hL : 2 ≤ L) (depth : ℕ) (spacing epsilon a : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
    FinitePiLpFiniteRange
      (scratch_cmp89SourceSeparatedFinePrefixPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall)
      (fun x y : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
        finBoxDist x.1 y.1)
      (L ^ (depth + 1)) := by
  dsimp only
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  intro source target v hfar
  change L ^ (depth + 1) < finBoxDist target.1 source.1 at hfar
  have hpowPos : 0 < L ^ (depth + 1) := pow_pos (NeZero.pos L) _
  have hlapFar : 1 < finBoxDist target.1 source.1 := by omega
  have hlap := cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
    (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing source target v hlapFar
  dsimp only [Omega] at hlap
  have hmassFar : L ^ (depth + 1) - 1 <
      finBoxDist target.1 source.1 := by omega
  have hmass :=
    scratch_cmp89SourceSeparatedFinalPrefix_QprimeMass_finiteRange
      hL depth spacing epsilon background budget fineSmall
        source target v hmassFar
  rw [scratch_cmp89SourceSeparatedFinePrefixPrecision,
    scratch_cmp85SourceGeneratedPrefixPrecision,
    scratch_cmp85BareMassPrecision, cmp99SourceGaugePrecision]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [scratch_cmp89SourceSeparatedFinalPrefixQprimeMass,
    scratch_cmp89SourceSeparatedPrefixTower] at hmass
  rw [hlap, hmass]
  simp

/-- Operator-norm budget for the exact prefix precision. -/
theorem scratch_norm_cmp89SourceSeparatedFinePrefixPrecision_le
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
        spacing epsilon a background budget fineSmall‖ ≤
      scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
        spacing epsilon a background budget fineSmall := by
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let T := scratch_cmp89SourceSeparatedPrefixTower
    (spacing := spacing) (epsilon := epsilon) hL depth background budget
    fineSmall
  let r := scratch_cmp85LastPositivePrefix (depth + 1)
    (Nat.succ_pos depth)
  let b := scratch_cmp85SourcePrefixCountingCoefficient T a r
  have hQ : ‖(T.towerAt r.1).Qprime‖ ≤ 1 := by
    exact scratch_norm_cmp89SourceSeparatedFinalPrefix_Qprime_le_one
      hL depth hspacing background budget fineSmall
  have hDelta := norm_cmp99ActiveRegionSourceCovariantLaplacian_le
    (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background hspacing
  rw [scratch_cmp89SourceSeparatedFinePrefixPrecision,
    scratch_cmp85SourceGeneratedPrefixPrecision,
    scratch_cmp85BareMassPrecision, cmp99SourceGaugePrecision]
  unfold scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
  change ‖cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
        (matrixSUNAdjointModel Nc) background spacing +
      0 ^ 2 • ContinuousLinearMap.id ℝ _ +
      b • ((T.towerAt r.1).Qprime.adjoint.comp
        (T.towerAt r.1).Qprime)‖ ≤ 16 / spacing ^ 2 + |b|
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul, add_zero]
  calc
    ‖cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing +
        b • ((T.towerAt r.1).Qprime.adjoint.comp
          (T.towerAt r.1).Qprime)‖ ≤
      ‖cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1))
          (matrixSUNAdjointModel Nc) background spacing‖ +
        ‖b • ((T.towerAt r.1).Qprime.adjoint.comp
          (T.towerAt r.1).Qprime)‖ := norm_add_le _ _
    _ ≤ 4 * (4 : ℝ) / spacing ^ 2 +
        |b| * ‖(T.towerAt r.1).Qprime‖ ^ 2 := by
      rw [norm_smul, ContinuousLinearMap.norm_adjoint_comp_self,
        Real.norm_eq_abs]
      simpa only [pow_two] using add_le_add hDelta
        (le_refl (|b| *
          (‖(T.towerAt r.1).Qprime‖ * ‖(T.towerAt r.1).Qprime‖)))
    _ = 16 / spacing ^ 2 + |b| * ‖(T.towerAt r.1).Qprime‖ ^ 2 := by
      norm_num
    _ ≤ 16 / spacing ^ 2 + |b| := by
      have hQsq : ‖(T.towerAt r.1).Qprime‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (T.towerAt r.1).Qprime]
      exact add_le_add_right
        (by simpa using mul_le_mul_of_nonneg_left hQsq (abs_nonneg b)) _

/-- Entrywise kernel bound obtained from the exact operator-norm budget. -/
theorem scratch_cmp89SourceSeparatedFinePrefixPrecision_kernelBound
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpKernelBound
      (scratch_cmp89SourceSeparatedFinePrefixPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall)
      (fun _ _ =>
        scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
          spacing epsilon a background budget fineSmall) := by
  apply finitePiLpKernelBound_of_opNorm_le
  exact scratch_norm_cmp89SourceSeparatedFinePrefixPrecision_le
    hL depth hspacing background budget fineSmall

/-- Per-depth CT bound for the exact P5 fine Green.  The rate budget is a
visible analytic condition, not hidden in a generated constant. -/
theorem scratch_cmp89SourceSeparatedFinePrefixGreen_exponentialKernelBound
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a rate : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (hrate : 0 < rate)
    (hbudget :
      scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
          spacing epsilon a background budget fineSmall *
        (Real.exp (rate * (L ^ (depth + 1) : ℕ)) - 1) *
        (((2 * L ^ (depth + 1) + 1) ^ 4 : ℕ) : ℝ) ≤
      scratch_cmp89SourceSeparatedPrefixCoercivity
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
          spacing epsilon a background budget fineSmall / 2) :
    let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
    FinitePiLpExponentialKernelBound
      (scratch_cmp89SourceSeparatedFinePrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth hspacing ha
        background budget fineSmall hsmall)
      (fun x y : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
        finBoxDist x.1 y.1)
      (2 / scratch_cmp89SourceSeparatedPrefixCoercivity
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall)
      rate := by
  dsimp only
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let Kfine := scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
    spacing epsilon a background budget fineSmall
  let Cfine := scratch_cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
    background budget fineSmall hsmall
  apply finitePiLpExponentialKernelBound_of_coercive
    (fun x y : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
      finBoxDist x.1 y.1)
    (fun p q => finBoxDist_comm p.1 q.1)
    (fun p q r => finBoxDist_triangle p.1 q.1 r.1)
    (fun p => finBoxDist_self p.1)
    hrate
    (scratch_cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall)
    (scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
      hspacing background budget fineSmall).le
    (R := L ^ (depth + 1))
    (NR := (2 * L ^ (depth + 1) + 1) ^ 4)
    (fun x => activeGaugeRegion_finBoxDist_ball_card_le
      (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) x _)
    Kfine Cfine
  · exact scratch_cmp89SourceSeparatedFinePrefixPrecision_finiteRange
      hL depth spacing epsilon a background budget fineSmall
  · exact scratch_cmp89SourceSeparatedFinePrefixPrecision_kernelBound
      hL depth hspacing background budget fineSmall
  · exact scratch_isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL Omega (depth + 1) hspacing ha 0 background
      budget.toRadiusChain fineSmall hsmall
      (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))
  · exact scratch_cmp85SourceGeneratedPrefixPrecision_comp_green
      (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
      (by norm_num) hL Omega (depth + 1) hspacing ha 0 background
      budget.toRadiusChain fineSmall hsmall
      (scratch_cmp85LastPositivePrefix (depth + 1) (Nat.succ_pos depth))
  · exact hbudget

/-- The same exact CT estimate on P5's separated ambient carrier. -/
theorem scratch_cmp89SourceSeparatedAmbientPrefixGreen_exponentialKernelBound
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a rate : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (hrate : 0 < rate)
    (hbudget :
      scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
          spacing epsilon a background budget fineSmall *
        (Real.exp (rate * (L ^ (depth + 1) : ℕ)) - 1) *
        (((2 * L ^ (depth + 1) + 1) ^ 4 : ℕ) : ℝ) ≤
      scratch_cmp89SourceSeparatedPrefixCoercivity
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
          spacing epsilon a background budget fineSmall / 2) :
    FinitePiLpExponentialKernelBound
      (scratch_cmp89SourceSeparatedAmbientPrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth hspacing ha
        background budget fineSmall hsmall)
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ)
      (2 / scratch_cmp89SourceSeparatedPrefixCoercivity
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall)
      rate := by
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let Cfine := scratch_cmp89SourceSeparatedFinePrefixGreen hL depth hspacing ha
    background budget fineSmall hsmall
  have hfine :=
    scratch_cmp89SourceSeparatedFinePrefixGreen_exponentialKernelBound
      hL depth hspacing ha background budget fineSmall hsmall hrate hbudget
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex e e Cfine
    (fun target source : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
      finBoxDist target.1 source.1) hfine
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ) := by
    funext target source
    exact finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
      L K Q depth target source
  rw [hdist] at hreindexed
  exact hreindexed

/-- Finite-range localization of the exact ambient precision, used as the
input to the canonical regional inverse theorem. -/
theorem scratch_cmp89SourceSeparatedAmbientPrefixPrecision_exponentialKernelBound
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a decay : ℝ}
    (hspacing : 0 < spacing) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpExponentialKernelBound
      (scratch_cmp89SourceSeparatedAmbientPrefixPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall)
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ)
      (scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
          spacing epsilon a background budget fineSmall *
        Real.exp (decay * (L ^ (depth + 1) : ℕ)))
      decay := by
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let e := cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let Kfine := scratch_cmp89SourceSeparatedFinePrefixPrecision hL depth
    spacing epsilon a background budget fineSmall
  have hfine : FinitePiLpExponentialKernelBound Kfine
      (fun target source : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
        finBoxDist target.1 source.1)
      (scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
          spacing epsilon a background budget fineSmall *
        Real.exp (decay * (L ^ (depth + 1) : ℕ))) decay := by
    apply finitePiLpTypedExponentialKernelBound_of_finiteRange
      (beta := scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
        spacing epsilon a background budget fineSmall)
      (R := L ^ (depth + 1))
    · exact (scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
        hspacing background budget fineSmall).le
    · exact hdecay
    · exact scratch_cmp89SourceSeparatedFinePrefixPrecision_finiteRange
        hL depth spacing epsilon a background budget fineSmall
    · exact scratch_cmp89SourceSeparatedFinePrefixPrecision_kernelBound
        hL depth hspacing background budget fineSmall
  have hreindexed := finitePiLpTypedExponentialKernelBound_reindex e e Kfine
    (fun target source : ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)) =>
      finBoxDist target.1 source.1) hfine
  have hdist :
      (fun target source : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) =>
        finBoxDist (e.symm target).1 (e.symm source).1) =
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ) := by
    funext target source
    exact finBoxDist_cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv_symm
      L K Q depth target source
  rw [hdist] at hreindexed
  exact hreindexed

/-- P8's canonical local Green inherits a per-depth exponential bound from
the one exact ambient prefix precision. -/
theorem scratch_cmp96SourceSeparatedRegionalPrefixGreen_exponentialKernelBound
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a decay : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    let A := scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (L ^ (depth + 1) : ℕ))
    let c := scratch_cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    FinitePiLpExponentialKernelBound
      (scratch_cmp96SourceSeparatedRegionalPrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth hspacing ha
        background budget fineSmall hsmall cell)
      (fun target source : ActiveGaugeRegion.Site
          (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell) =>
        finBoxDist target.1 source.1)
      (2 / c)
      (finitePiLpExponentialInverseDecayRate A decay
        (cmp99OmegaSiteExpSumBound (decay / 4)) c) := by
  dsimp only
  let A := scratch_cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (L ^ (depth + 1) : ℕ))
  let c := scratch_cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  exact cmp99RegionalDirichletGreen_exponentialKernelBound
    (scratch_cmp96SourceSeparatedRegionalCell P L K Q depth cell)
    (scratch_cmp89SourceSeparatedAmbientPrefixPrecision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall)
    (scratch_cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall)
    (scratch_isCoerciveCLM_cmp89SourceSeparatedAmbientPrefixPrecision
      hL depth hspacing ha background budget fineSmall hsmall)
    (scratch_cmp89SourceSeparatedAmbientPrefixPrecision_exponentialKernelBound
      hL depth hspacing hdecay background budget fineSmall)

end

end YangMills.RG
