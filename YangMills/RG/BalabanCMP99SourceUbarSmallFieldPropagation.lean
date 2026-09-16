/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalScale
import YangMills.RG.SUNProductDeviation

/-!
# Propagation of source smallness through one physical Ubar step

The recursive source tower must not receive a new small-field certificate at
each level.  This file derives it from the preceding fine background.  The
proof first controls the normalized average of principal logarithms, then the
operator exponential, and finally multiplies by the straight coarse
transport.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance matrixL2CStarAlgebraForSourcePropagation :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

local instance matrixRealComplexScalarTowerForSourcePropagation :
    IsScalarTower ℝ ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) where
  smul_assoc r c X := by
    ext i j
    exact smul_assoc r c (X i j)

/-- Logarithmic radius induced by a deviation budget. -/
def cmp99UbarLogRadius (B : MatrixNearLogNoWindingBudget Nc) : ℝ :=
  B.δ / (1 - B.δ)

/-- Exponential deviation radius obtained from the second-order Banach
algebra exponential estimate. -/
def cmp99UbarExpRadius (B : MatrixNearLogNoWindingBudget Nc) : ℝ :=
  cmp99UbarLogRadius B +
    cmp99UbarLogRadius B ^ 2 / (1 - cmp99UbarLogRadius B)

/-- A convex weighted average of the physical principal logarithms is
bounded by the budget's sharp logarithmic radius. -/
theorem norm_cmp99UbarSpecialUnitaryExponent_le_logRadius
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    ‖cmp99UbarSpecialUnitaryExponent s w D‖ ≤ cmp99UbarLogRadius B := by
  unfold cmp99UbarSpecialUnitaryExponent cmp99UbarUnitaryExponent
    cmp99UbarExponent
  calc
    ‖∑ i ∈ s, w i •
        nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖
        ≤ ∑ i ∈ s, ‖w i •
          nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w i * cmp99UbarLogRadius B := by
      apply Finset.sum_le_sum
      intro i hi
      have hsmul :
          w i • nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) =
            (w i : ℂ) •
              nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
        ext p q
        simp [RCLike.real_smul_eq_coe_mul]
      rw [hsmul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw_nonneg i hi)]
      exact mul_le_mul_of_nonneg_left
        (norm_nearLog_le_div_of_norm_le B.δ_lt_one (hdev i hi))
        (hw_nonneg i hi)
    _ = cmp99UbarLogRadius B := by
      rw [← Finset.sum_mul, hw_sum, one_mul]

/-- The special-unitary exponential factor remains explicitly close to one.
The extra condition `logRadius < 1` is the genuine scalar small-field budget
needed by the Banach-algebra exponential remainder, not a renamed conclusion.
-/
theorem norm_cmp99UbarSpecialUnitaryFactorOfDeviationBudget_sub_one_le
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hlog : cmp99UbarLogRadius B < 1) :
    ‖(cmp99UbarSpecialUnitaryFactorOfDeviationBudget
        s w D B hdev : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99UbarExpRadius B := by
  let Z := cmp99UbarSpecialUnitaryExponent s w D
  have hZ : ‖Z‖ ≤ cmp99UbarLogRadius B :=
    norm_cmp99UbarSpecialUnitaryExponent_le_logRadius
      s w D B hdev hw_nonneg hw_sum
  have hZlt : ‖Z‖ < 1 := lt_of_le_of_lt hZ hlog
  have hlog_nonneg : 0 ≤ cmp99UbarLogRadius B :=
    le_trans (norm_nonneg Z) hZ
  have hdenZ : 0 < 1 - ‖Z‖ := sub_pos.mpr hZlt
  have hdenLog : 0 < 1 - cmp99UbarLogRadius B := sub_pos.mpr hlog
  rw [cmp99UbarSpecialUnitaryFactorOfDeviationBudget_coe]
  change ‖NormedSpace.exp Z - 1‖ ≤ cmp99UbarExpRadius B
  calc
    ‖NormedSpace.exp Z - 1‖
        = ‖(NormedSpace.exp Z - 1 - Z) + Z‖ := by congr 1; abel
    _ ≤ ‖NormedSpace.exp Z - 1 - Z‖ + ‖Z‖ := norm_add_le _ _
    _ ≤ ‖Z‖ ^ 2 / (1 - ‖Z‖) + ‖Z‖ := by
      gcongr
      exact norm_exp_sub_one_sub_self_le hZlt
    _ ≤ cmp99UbarLogRadius B ^ 2 /
          (1 - cmp99UbarLogRadius B) + cmp99UbarLogRadius B := by
      apply add_le_add _ hZ
      calc
        ‖Z‖ ^ 2 / (1 - ‖Z‖) ≤
            cmp99UbarLogRadius B ^ 2 / (1 - ‖Z‖) := by
          exact div_le_div_of_nonneg_right
            (sq_le_sq₀ (norm_nonneg Z) hlog_nonneg |>.2 hZ)
            hdenZ.le
        _ ≤ cmp99UbarLogRadius B ^ 2 /
            (1 - cmp99UbarLogRadius B) := by
          exact div_le_div_of_nonneg_left (sq_nonneg _)
            hdenLog (by linarith)
    _ = cmp99UbarExpRadius B := by
      rw [cmp99UbarExpRadius]
      ring

/-- A normalized physical Ubar block inherits the exponential radius plus
the deviation of its coarse base transport. -/
theorem norm_cmp99UbarSpecialUnitaryBlockOfDeviationBudget_sub_one_le
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hlog : cmp99UbarLogRadius B < 1)
    (coarse : SUN Nc) (epsilonCoarse : ℝ)
    (hcoarse :
      ‖(coarse : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    ‖(cmp99UbarSpecialUnitaryBlockOfDeviationBudget
        s w D B hdev coarse : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99UbarExpRadius B + epsilonCoarse := by
  exact (norm_sun_mul_sub_one_le
    (cmp99UbarSpecialUnitaryFactorOfDeviationBudget s w D B hdev)
    coarse).trans (add_le_add
      (norm_cmp99UbarSpecialUnitaryFactorOfDeviationBudget_sub_one_le
        s w D B hdev hw_nonneg hw_sum hlog)
      hcoarse)

variable {d M N' : ℕ} [NeZero d] [NeZero M] [NeZero N']

/-- Radius propagated to the next group-valued source background. -/
def cmp99SourceUbarNextFineRadius (d M : ℕ) (epsilonFine : ℝ) : ℝ :=
  let delta := cmp99SourceUbarFineDeviationRadius d M epsilonFine
  let theta := delta / (1 - delta)
  theta + theta ^ 2 / (1 - theta) + (M : ℝ) * epsilonFine

/-- The source block weights over a complete block form a probability
vector. -/
theorem sum_cmp99SourceBlockAverageWeight_blockOf
    (y : FinBox d N') :
    ∑ _x ∈ blockOf M N' y, cmp99SourceBlockAverageWeight M d = 1 := by
  rw [Finset.sum_const, blockOf_card]
  simp only [nsmul_eq_mul, Nat.cast_pow,
    cmp99SourceBlockAverageWeight]
  have hMreal : (M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne M)
  exact mul_inv_cancel₀ (pow_ne_zero d hMreal)

/-- One source Ubar block is small at the next explicit radius. -/
theorem norm_cmp99PhysicalUbarBlockOfFineSmall_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : GaugeConfig d (M * N') (SUN Nc))
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (b : PhysicalBond d N') :
    ‖(cmp99PhysicalUbarBlockOfDeviationBudget
        background (cmp99SourceBaseCoarseBackground background)
        (cmp99SourceUbarGamma1 (G := SUN Nc))
        (cmp99SourceUbarGamma2 (G := SUN Nc))
        (cmp99SourceUbarGamma3 (G := SUN Nc))
        (cmp99SourceUbarFineNoWindingBudget
          (d := d) (M := M) (Nc := Nc) epsilonFine noWinding)
        (cmp99SourceRegionalScaleDataOfFineSmall hd hM
          (ActiveGaugeRegion.mk Finset.univ) background 1 epsilonFine
          epsilonFine_nonneg noWinding fine_small).deviation_bound b :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilonFine := by
  let B := cmp99SourceUbarFineNoWindingBudget
    (d := d) (M := M) (Nc := Nc) epsilonFine noWinding
  let D : FinBox d (M * N') → SUN Nc := fun x =>
    UbarDeviation background (cmp99SourceBaseCoarseBackground background)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b)
  let S := blockOf M N' b.1
  have hdev : ∀ x ∈ S,
      ‖(D x : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ := by
    intro x hx
    simpa [B, D, UbarDeviationLogArg] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
        hd hM background epsilonFine epsilonFine_nonneg fine_small b x hx
  have hblock := norm_cmp99UbarSpecialUnitaryBlockOfDeviationBudget_sub_one_le
    S (fun _ => cmp99SourceBlockAverageWeight M d) D B hdev
    (fun _ _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg M) d))
    (sum_cmp99SourceBlockAverageWeight_blockOf (M := M) b.1)
    (by simpa [B] using logSmall)
    (cmp99SourceBaseCoarseBackground background
      (positiveEdgeOfPhysicalBond b)) ((M : ℝ) * epsilonFine)
    (norm_cmp99SourceBaseCoarseBackground_sub_one_le
      background epsilonFine fine_small b)
  simpa [cmp99PhysicalUbarBlockOfDeviationBudget, S, D, B,
    cmp99SourceUbarNextFineRadius, cmp99UbarExpRadius,
    cmp99UbarLogRadius, cmp99SourceUbarFineNoWindingBudget_delta]
    using hblock

/-- The canonical next background is uniformly small on every oriented
link.  Negative links cost nothing: inversion preserves distance from the
identity in the defining special-unitary representation. -/
theorem norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (e : ConcreteEdge d N') :
    ‖((cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
          weight epsilonFine epsilonFine_nonneg noWinding fine_small).nextBackground e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilonFine := by
  rcases e with ⟨y, mu, orient⟩
  cases orient with
  | false =>
      rw [CMP99PhysicalRegionalScaleData.nextBackground,
        cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_neg]
      exact (norm_sun_inv_sub_one_le _).trans
        (norm_cmp99PhysicalUbarBlockOfFineSmall_sub_one_le hd hM
          background epsilonFine epsilonFine_nonneg noWinding logSmall
          fine_small (y, mu))
  | true =>
      change
        ‖((cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
              weight epsilonFine epsilonFine_nonneg noWinding fine_small).nextBackground
              (positiveEdgeOfPhysicalBond (y, mu)) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          cmp99SourceUbarNextFineRadius d M epsilonFine
      rw [CMP99PhysicalRegionalScaleData.nextBackground,
        cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_pos]
      exact norm_cmp99PhysicalUbarBlockOfFineSmall_sub_one_le hd hM
        background epsilonFine epsilonFine_nonneg noWinding logSmall
        fine_small (y, mu)

end

end YangMills.RG
