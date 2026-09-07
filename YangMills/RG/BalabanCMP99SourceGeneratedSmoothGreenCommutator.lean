/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpScalarCommutator
import YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas
import YangMills.RG.BalabanCMP99SourceGeneratedGreenTransitionDecay

/-!
# The smooth generated Green commutator in CMP99 Section C

CMP95 (1.118), imported in CMP96 (2.36), puts the smooth partition on cubes
one blocking scale larger than the terminal fine-to-coarse block.  On the
generated fine lattice this means the literal length
`M0 = M^(depth+2)`, whereas the terminal block has side `M^(depth+1)`.

This file inserts that source scale and the generated physical Green into the
exact commutator `[G',(h')^2]` printed in CMP99 p. 412.  The only remaining
input is the geometric coordinate chart on the finite torus.  It is stated
as the exact comparison that the forthcoming periodic lift must prove; no
operator estimate is supplied through it.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M N Nc depth : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

/-- Literal source scale of the smooth partition on the generated fine
lattice: one order-`M` blocking larger than the terminal regional block. -/
def cmp99SourceGeneratedSmoothCutoffScale (M depth : ℕ) : ℝ :=
  (M ^ (depth + 2) : ℕ)

theorem cmp99SourceGeneratedSmoothCutoffScale_pos
    (M depth : ℕ) [NeZero M] :
    0 < cmp99SourceGeneratedSmoothCutoffScale M depth := by
  unfold cmp99SourceGeneratedSmoothCutoffScale
  exact_mod_cast pow_pos (NeZero.pos M) (depth + 2)

/-- Canonical generated fine-lattice location of the source cell `Pi`.
The cell coordinate is first embedded as the lower corner `2 * cell` of its
two-large-block source cube, and then as the lower corner of the terminal
order-`M^(depth+1)` fine block.  This is the finite-torus representative of
the translate index used by the CMP95 profile. -/
def cmp99SourceGeneratedSmoothCutoffCenter
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q) :
    FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) :=
  fun i => Fin.cast
    (cmp99RegionalLatticeSize_eq_pow_mul M (2 * Q) (depth + 1)).symm
    (blockBasepoint (M ^ (depth + 1)) (2 * Q)
      (blockBasepoint 2 Q cell) i)

@[simp] theorem cmp99SourceGeneratedSmoothCutoffCenter_val
    (M Q depth : ℕ) [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q) (i : Fin 4) :
    (cmp99SourceGeneratedSmoothCutoffCenter M Q depth cell i).val =
      M ^ (depth + 1) * (2 * (cell i).val) := by
  simp [cmp99SourceGeneratedSmoothCutoffCenter, blockBasepoint]

/-- A canonical real coordinate attached to a periodic site: circular
distance from a fixed centre in each coordinate.  Unlike the raw `Fin.val`
coordinate, this chart has no artificial jump across the chosen fundamental
domain. -/
def finTorusDistanceCoordinates {d L : ℕ}
    (center x : FinBox d L) : Fin d → ℝ :=
  fun i => finTorusDist (center i) (x i)

/-- Reverse triangle inequality for one circular coordinate, in the real
norm used by the smooth profile. -/
theorem norm_finTorusDistanceCoordinates_sub_le
    {d L : ℕ} [NeZero L] (center x y : FinBox d L) (i : Fin d) :
    ‖finTorusDistanceCoordinates center x i -
        finTorusDistanceCoordinates center y i‖ ≤
      finTorusDist (x i) (y i) := by
  have hcx : finTorusDist (center i) (x i) ≤
      finTorusDist (center i) (y i) + finTorusDist (y i) (x i) :=
    finTorusDist_triangle _ _ _
  have hcy : finTorusDist (center i) (y i) ≤
      finTorusDist (center i) (x i) + finTorusDist (x i) (y i) :=
    finTorusDist_triangle _ _ _
  have hcxR0 : (finTorusDist (center i) (x i) : ℝ) ≤
      ((finTorusDist (center i) (y i) +
        finTorusDist (x i) (y i) : ℕ) : ℝ) :=
    Nat.cast_le.2 (by simpa [finTorusDist_comm] using hcx)
  have hcxR : (finTorusDist (center i) (x i) : ℝ) ≤
      finTorusDist (center i) (y i) + finTorusDist (x i) (y i) := by
    simpa only [Nat.cast_add] using hcxR0
  have hcyR0 : (finTorusDist (center i) (y i) : ℝ) ≤
      ((finTorusDist (center i) (x i) +
        finTorusDist (x i) (y i) : ℕ) : ℝ) :=
    Nat.cast_le.2 hcy
  have hcyR : (finTorusDist (center i) (y i) : ℝ) ≤
      finTorusDist (center i) (x i) + finTorusDist (x i) (y i) := by
    simpa only [Nat.cast_add] using hcyR0
  change ‖(finTorusDist (center i) (x i) : ℝ) -
      (finTorusDist (center i) (y i) : ℝ)‖ ≤
    (finTorusDist (x i) (y i) : ℝ)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- In four dimensions the canonical circular-distance coordinates have
`ℓ¹` slope at most four times the physical Chebyshev torus distance. -/
theorem sum_norm_finTorusDistanceCoordinates_sub_le_four_finBoxDist
    {L : ℕ} [NeZero L] (center x y : FinBox 4 L) :
    (∑ i, ‖finTorusDistanceCoordinates center x i -
        finTorusDistanceCoordinates center y i‖) ≤
      4 * (finBoxDist x y : ℝ) := by
  calc
    (∑ i, ‖finTorusDistanceCoordinates center x i -
        finTorusDistanceCoordinates center y i‖) ≤
        ∑ _i : Fin 4, (finBoxDist x y : ℝ) := by
      gcongr with i
      exact (norm_finTorusDistanceCoordinates_sub_le center x y i).trans
        (Nat.cast_le.2 (finTorusDist_le_finBoxDist x y i))
    _ = 4 * (finBoxDist x y : ℝ) := by simp

/-- The literal generated physical operator `[G',(h_z')²]`. -/
noncomputable def cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let G := cmp99SourceGeneratedPhysicalGreen
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  let h := fun x => P.tensorCutoff
    (cmp99SourceGeneratedSmoothCutoffScale M depth) center (coord x)
  finitePiLpOperatorScalarCommutator G (fun x => h x ^ 2)

/-- The unsquared source commutator `[G',h'_Pi]` which controls the basic
factor `K(h'_Pi) G'_Pi h'_Pi` on CMP99 printed p. 412. -/
noncomputable def cmp99SourceGeneratedPhysicalGreenSmoothCommutator
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let G := cmp99SourceGeneratedPhysicalGreen
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  let h := fun x => P.tensorCutoff
    (cmp99SourceGeneratedSmoothCutoffScale M depth) center (coord x)
  finitePiLpOperatorScalarCommutator G h

/-- Pointwise decay of `[G',h'_Pi]`.  The source derivative scale is exposed
before the factor is multiplied by the precision and the final cutoff. -/
theorem cmp99SourceGeneratedPhysicalGreenSmoothCommutator_exponential
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        4 * (finBoxDist target.1 source.1 : ℝ))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalGreenSmoothCommutator
        P Omega center coord hM hspacing background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      ((2 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
  unfold cmp99SourceGeneratedPhysicalGreenSmoothCommutator
  rw [finitePiLpOperatorScalarCommutator_eq_neg]
  apply finitePiLpTypedExponentialKernelBound_neg
  apply finitePiLpScalarCommutator_tensorCutoff_exponentialKernelBound
    P (cmp99SourceGeneratedSmoothCutoffScale_pos M depth) center coord
      (fun x y => finBoxDist x.1 y.1) (by norm_num : (0 : ℝ) ≤ 4) hcoord
  exact cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall

/-- Volume-independent operator norm of `[G',h'_Pi]`, retaining the literal
`M0^-1` slope from CMP95 (1.118). -/
theorem norm_cmp99SourceGeneratedPhysicalGreenSmoothCommutator_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        4 * (finBoxDist target.1 source.1 : ℝ))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalGreenSmoothCommutator
        P Omega center coord hM hspacing background budget fineSmall hsmall‖ ≤
      ((2 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
      cmp99OmegaSiteExpSumBound
        (cmp99SourceGeneratedCombesThomasRate
          4 M depth spacing epsilon / 2) := by
  let rate := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  have hrate : 0 < rate :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hrowNonneg : 0 ≤ cmp99OmegaSiteExpSumBound (rate / 2) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ => mul_nonneg (by positivity) (Real.exp_pos _).le
  apply finitePiLpOpNorm_le_of_exponentialKernelBound
    _ (fun x y => finBoxDist x.1 y.1)
    (fun x y => finBoxDist_comm x.1 y.1) hrowNonneg
  · exact cmp99SourceGeneratedPhysicalGreenSmoothCommutator_exponential
      P Omega center coord hcoord hM hspacing background budget fineSmall hsmall
  · intro x
    exact activeGaugeRegion_finBoxDist_exp_sum_le
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) x
      (div_pos hrate zero_lt_two)

/-- Pointwise exponential decay of the literal generated commutator.  The
factor `4` is the four-dimensional `ℓ¹`/Chebyshev comparison, and all analytic
constants are generated internally. -/
theorem cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_exponential
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        4 * (finBoxDist target.1 source.1 : ℝ))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
        P Omega center coord hM hspacing background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      ((4 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
  unfold cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
  apply finitePiLpOperatorScalarCommutator_tensorCutoff_sq_exponentialKernelBound
    P (cmp99SourceGeneratedSmoothCutoffScale_pos M depth) center coord
      (fun x y => finBoxDist x.1 y.1) (by norm_num : (0 : ℝ) ≤ 4) hcoord
  exact cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall

/-- The commutator is `O(M0⁻¹)` in operator norm, with the explicit
volume-independent four-dimensional shell sum. -/
theorem norm_cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : Fin 4 → ℝ)
    (coord : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) →
        Fin 4 → ℝ)
    (hcoord : ∀ target source,
      (∑ μ, ‖coord target μ - coord source μ‖) ≤
        4 * (finBoxDist target.1 source.1 : ℝ))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
        P Omega center coord hM hspacing background budget fineSmall hsmall‖ ≤
      ((4 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
      cmp99OmegaSiteExpSumBound
        (cmp99SourceGeneratedCombesThomasRate
          4 M depth spacing epsilon / 2) := by
  let rate := cmp99SourceGeneratedCombesThomasRate
    4 M depth spacing epsilon
  have hrate : 0 < rate :=
    cmp99SourceGeneratedCombesThomasRate_pos 4 M depth hspacing hsmall
  have hrowNonneg : 0 ≤ cmp99OmegaSiteExpSumBound (rate / 2) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ => mul_nonneg (by positivity) (Real.exp_pos _).le
  apply finitePiLpOpNorm_le_of_exponentialKernelBound
    _ (fun x y => finBoxDist x.1 y.1)
    (fun x y => finBoxDist_comm x.1 y.1) hrowNonneg
  · exact cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_exponential
      P Omega center coord hcoord hM hspacing background budget fineSmall hsmall
  · intro x
    exact activeGaugeRegion_finBoxDist_exp_sum_le
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) x
      (div_pos hrate zero_lt_two)

/-- Chart-free periodic specialization of the pointwise estimate.  It uses
the circular distance from `center` in every coordinate, so no fundamental-
domain seam remains as an input.  This realizes the analytic cutoff estimate;
identification of this representative with the complete translated square
partition of CMP95 (1.118) is deliberately not asserted here. -/
theorem
    cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_exponential_torusDistance
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : FinBox 4 (cmp99RegionalLatticeSize M N (depth + 1)))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
        P Omega (fun _ => 0)
          (fun x => finTorusDistanceCoordinates center x.1)
          hM hspacing background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      ((4 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate
        4 M depth spacing epsilon / 2) := by
  apply cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_exponential
  intro target source
  exact sum_norm_finTorusDistanceCoordinates_sub_le_four_finBoxDist
    center target.1 source.1

/-- The corresponding volume-independent operator-norm estimate with no
caller-supplied coordinate comparison. -/
theorem
    norm_cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_torusDistance_le
    (P : CMP95SourceSmoothPartitionProfile)
    (Omega : ActiveGaugeRegion 4 N)
    (center : FinBox 4 (cmp99RegionalLatticeSize M N (depth + 1)))
    (hM : 2 ≤ M) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator
        P Omega (fun _ => 0)
          (fun x => finTorusDistanceCoordinates center x.1)
          hM hspacing background budget fineSmall hsmall‖ ≤
      ((4 * ((P.derivBound /
          cmp99SourceGeneratedSmoothCutoffScale M depth) * 4) *
            (2 / cmp99SourceGeneratedCoercivity
              4 M (depth + 1) spacing epsilon)) /
        cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon) *
      cmp99OmegaSiteExpSumBound
        (cmp99SourceGeneratedCombesThomasRate
          4 M depth spacing epsilon / 2) := by
  apply norm_cmp99SourceGeneratedPhysicalGreenSmoothSquareCommutator_le
  intro target source
  exact sum_norm_finTorusDistanceCoordinates_sub_le_four_finBoxDist
    center target.1 source.1

end

end YangMills.RG
