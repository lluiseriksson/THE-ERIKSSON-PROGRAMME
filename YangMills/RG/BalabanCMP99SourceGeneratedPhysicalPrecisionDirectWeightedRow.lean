/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCountingMassRow
import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.FinitePiLpTypedWeightedRowFromRange

/-!
# Direct weighted rows of the generated CMP99 physical precision

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The source precision is the literal sum of a nearest-neighbour covariant
Laplacian and the normalized mass `a_j Q'^* Q'`.  Reconstructing a row of the
whole precision from its terminal range would introduce a false block-ball
factor.  This module instead bounds the two printed summands separately:

* the Laplacian pays only its one-link ball;
* `Q'^* Q'` uses the exact row mass `(M^{-d})^(depth+1)`;
* the scalar mass and the two rows are combined algebraically.

Thus the terminal range appears only inside the exponential weight of the
normalized mass row, never as a cardinality factor.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

/-- Scalar multiplication preserves a weighted-row estimate with the exact
absolute scalar cost. -/
theorem finitePiLpTypedWeightedRowKernelBound_smul
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (c : ℝ) {T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A rate : ℝ}
    (hT : FinitePiLpTypedWeightedRowKernelBound T dist A rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (c • T) dist (|c| * A) rate := by
  refine ⟨mul_nonneg (abs_nonneg c) hT.1, hT.2.1, ?_⟩
  intro source v
  calc
    (∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(c • T) (singleFinitePiLp source v) target‖) =
        |c| * ∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro target _
      simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, norm_smul,
        Real.norm_eq_abs]
      ring
    _ ≤ |c| * (A * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hT.2.2 source v) (abs_nonneg c)
    _ = (|c| * A) * ‖v‖ := by ring

/-- Two weighted rows at the same spatial rate add without any hidden
cardinality cost. -/
theorem finitePiLpTypedWeightedRowKernelBound_add
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {S T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g}
    {dist : κ → ι → ℕ} {A B rate : ℝ}
    (hS : FinitePiLpTypedWeightedRowKernelBound S dist A rate)
    (hT : FinitePiLpTypedWeightedRowKernelBound T dist B rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (S + T) dist (A + B) rate := by
  refine ⟨add_nonneg hS.1 hT.1, hS.2.1, ?_⟩
  intro source v
  calc
    (∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖(S + T) (singleFinitePiLp source v) target‖) ≤
        ∑ target : κ,
          (Real.exp (rate * (dist target source : ℝ)) *
              ‖S (singleFinitePiLp source v) target‖ +
            Real.exp (rate * (dist target source : ℝ)) *
              ‖T (singleFinitePiLp source v) target‖) := by
      apply Finset.sum_le_sum
      intro target _
      rw [ContinuousLinearMap.add_apply, PiLp.add_apply]
      simpa only [mul_add] using
        (mul_le_mul_of_nonneg_left
          (norm_add_le
            (S (singleFinitePiLp source v) target)
            (T (singleFinitePiLp source v) target))
          (Real.exp_pos (rate * (dist target source : ℝ))).le)
    _ = (∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖S (singleFinitePiLp source v) target‖) +
        ∑ target : κ,
          Real.exp (rate * (dist target source : ℝ)) *
            ‖T (singleFinitePiLp source v) target‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ A * ‖v‖ + B * ‖v‖ :=
      add_le_add (hS.2.2 source v) (hT.2.2 source v)
    _ = (A + B) * ‖v‖ := by ring

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Fixed-rate cost of the literal nearest-neighbour Laplacian row.  Its
cardinality is the one-link ball `(2*1+1)^d`, independent of the generated
terminal scale. -/
noncomputable def cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
    (d : ℕ) (spacing rate : ℝ) : ℝ :=
  (4 * d / spacing ^ 2) * Real.exp rate * (3 : ℝ) ^ d

/-- The source covariant Laplacian has a direct volume-independent weighted
row at every nonnegative fixed rate. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_weightedRow
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (background : PhysicalGaugeBackground d N Nc)
    {spacing rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 ≤ rate) :
    FinitePiLpTypedWeightedRowKernelBound
      (ι := ActiveGaugeRegion.Site Omega)
      (κ := ActiveGaugeRegion.Site Omega)
      (g := SUNLieCoord Nc)
      (cmp99ActiveRegionSourceCovariantLaplacian
        Omega rho background spacing)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
        d spacing rate) rate := by
  let L := cmp99ActiveRegionSourceCovariantLaplacian
    Omega rho background spacing
  let beta : ℝ := 4 * d / spacing ^ 2
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    positivity
  have hfinite : FinitePiLpTypedFiniteRange L
      (fun target source => finBoxDist target.1 source.1) 1 := by
    exact cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
      Omega rho background spacing
  have hbound : FinitePiLpTypedKernelBound L (fun _ _ => beta) := by
    apply finitePiLpKernelBound_of_opNorm_le
    exact norm_cmp99ActiveRegionSourceCovariantLaplacian_le
      Omega rho background hspacing
  have hcard : ∀ source : ActiveGaugeRegion.Site Omega,
      (Finset.univ.filter (fun target : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1 ≤ 1)).card ≤ 3 ^ d := by
    intro source
    simpa [finBoxDist_comm] using
      activeGaugeRegion_finBoxDist_ball_card_le Omega source 1
  simpa [L, beta,
    cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude] using
      finitePiLpTypedWeightedRowKernelBound_of_finiteRange L
        (fun target source => finBoxDist target.1 source.1)
        1 (3 ^ d) hbeta hrate hfinite hbound hcard

/-- Direct fixed-rate amplitude of the complete generated physical precision.
The first summand is local; the second retains the exact normalized
`Q'^* Q'` row. -/
noncomputable def cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude
    (d M depth : ℕ) (spacing epsilon rate : ℝ) : ℝ :=
  cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
      d spacing rate +
    |cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon| *
      (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ (depth + 1))

/-- The complete literal generated precision has a weighted row whose mass
part contains no terminal range-ball cardinality. -/
theorem cmp99SourceGeneratedPhysicalPrecision_directWeightedRow
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing) (hrate : 0 ≤ rate)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpTypedWeightedRowKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (κ := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        background budget fineSmall)
      (fun target source => finBoxDist target.1 source.1)
      (cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude
        d M depth spacing epsilon rate) rate := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let L := cmp99ActiveRegionSourceCovariantLaplacian
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing
  let Qmass := T.Qprime.adjoint.comp T.Qprime
  let mass := cmp99SourceGeneratedPhysicalMass
    d M (depth + 1) spacing epsilon
  have hL : FinitePiLpTypedWeightedRowKernelBound L
      (fun target source => finBoxDist target.1 source.1)
      (cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude
        d spacing rate) rate := by
    exact cmp99ActiveRegionSourceCovariantLaplacian_weightedRow
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc) background hspacing hrate
  have hQ : FinitePiLpTypedWeightedRowKernelBound Qmass
      (fun target source => finBoxDist target.1 source.1)
      (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
        (cmp99SourceBlockAverageWeight M d) ^ (depth + 1)) rate := by
    simpa [regions, T, Qmass] using
      cmp99SourceIteratedLift_QprimeMass_weightedRow
        Omega (depth + 1) hd hM (matrixSUNAdjointModel Nc)
        spacing epsilon rate hrate background budget.toRadiusChain fineSmall
  have hmass : FinitePiLpTypedWeightedRowKernelBound (mass • Qmass)
      (fun target source => finBoxDist target.1 source.1)
      (|mass| *
        (Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)) *
          (cmp99SourceBlockAverageWeight M d) ^ (depth + 1))) rate :=
    finitePiLpTypedWeightedRowKernelBound_smul mass hQ
  have hsum := finitePiLpTypedWeightedRowKernelBound_add hL hmass
  rw [cmp99SourceGeneratedPhysicalPrecision, cmp99SourceGaugePrecision]
  simpa [regions, T, L, Qmass, mass,
    cmp99SourceGeneratedPhysicalPrecisionDirectWeightedRowAmplitude] using hsum

end

end YangMills.RG
