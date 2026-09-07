/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance
import YangMills.RG.PhysicalGaugeCochains

/-!
# The physical CMP99 gauge-transformation precision

CMP99 (3.23)--(3.24), printed pp. 394--395, uses the covariant site
derivative

`D_U^eta phi(b) = eta⁻¹ (R(U(b)) phi(b_+) - phi(b_-))`

and `Delta'_a = D_U^{eta*} D_U^eta + Q'† a Q'` with Dirichlet boundary.
The sign convention of `covariantD0CLM` is the negative of the printed
derivative and hence gives exactly the same Laplacian.

This file constructs that operator on each literal source region.  It also
proves the volume-independent stencil bound `‖D_U‖ ≤ 2 sqrt(d)` and consumes
the exact contraction estimate of the recursive source average.  Thus the
upper precision constant is generated internally.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Uniform squared-norm stencil estimate for the unscaled covariant site
derivative. -/
theorem norm_covariantD0CLM_sq_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc) :
    ‖covariantD0CLM rho U phi‖ ^ 2 ≤
      4 * (d : ℝ) * ‖phi‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    Fintype.sum_prod_type]
  have hpoint : ∀ (x : FinBox d N) (i : Fin d),
      ‖phi x - rho.adCLM (U (ConcreteEdge.mk x i true))
          (phi (x.shift i))‖ ^ 2 ≤
        2 * ‖phi x‖ ^ 2 + 2 * ‖phi (x.shift i)‖ ^ 2 := by
    intro x i
    have htri := norm_sub_le (phi x)
      (rho.adCLM (U (ConcreteEdge.mk x i true)) (phi (x.shift i)))
    rw [rho.norm_ad] at htri
    have hsqtri := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hab : (‖phi x‖ + ‖phi (x.shift i)‖) ^ 2 ≤
        2 * ‖phi x‖ ^ 2 + 2 * ‖phi (x.shift i)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖phi x‖ - ‖phi (x.shift i)‖)]
    exact hsqtri.trans hab
  have hsource :
      (∑ x : FinBox d N, ∑ _i : Fin d, ‖phi x‖ ^ 2) =
        (d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by
    calc
      (∑ x : FinBox d N, ∑ _i : Fin d, ‖phi x‖ ^ 2) =
          ∑ x : FinBox d N, (d : ℝ) * ‖phi x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp
      _ = (d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by
        rw [Finset.mul_sum]
  have htarget :
      (∑ x : FinBox d N, ∑ i : Fin d, ‖phi (x.shift i)‖ ^ 2) =
        (d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ i : Fin d, ∑ x : FinBox d N, ‖phi (x.shift i)‖ ^ 2) =
          ∑ i : Fin d, ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact FinBox.sum_shift (fun x : FinBox d N => ‖phi x‖ ^ 2) i
      _ = (d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by simp
  calc
    (∑ x : FinBox d N, ∑ i : Fin d,
        ‖covariantD0CLM rho U phi (x, i)‖ ^ 2) ≤
      ∑ x : FinBox d N, ∑ i : Fin d,
        (2 * ‖phi x‖ ^ 2 + 2 * ‖phi (x.shift i)‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro x _hx
          apply Finset.sum_le_sum
          intro i _hi
          exact hpoint x i
    _ = 2 * (∑ x : FinBox d N, ∑ i : Fin d, ‖phi x‖ ^ 2) +
        2 * (∑ x : FinBox d N, ∑ i : Fin d,
          ‖phi (x.shift i)‖ ^ 2) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
    _ = 2 * ((d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2) +
        2 * ((d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2) := by
      rw [hsource, htarget]
    _ = 4 * (d : ℝ) * ∑ x : FinBox d N, ‖phi x‖ ^ 2 := by ring

/-- Uniform operator norm of the unscaled covariant site derivative. -/
theorem norm_covariantD0CLM_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    ‖covariantD0CLM rho U‖ ≤ 2 * Real.sqrt d := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro phi
  have hsq := norm_covariantD0CLM_sq_le rho U phi
  have hsqrt : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (norm_nonneg _))).1
  calc
    ‖covariantD0CLM rho U phi‖ ^ 2 ≤ 4 * (d : ℝ) * ‖phi‖ ^ 2 := hsq
    _ = 4 * (Real.sqrt d) ^ 2 * ‖phi‖ ^ 2 := by rw [hsqrt]
    _ = (2 * Real.sqrt d * ‖phi‖) ^ 2 := by ring

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}

/-- The printed scaled covariant derivative on one Dirichlet source region.
Zero extension supplies the literal boundary condition. -/
noncomputable def cmp99OmegaSourceCovariantD0CLM
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc :=
  spacing⁻¹ •
    (covariantD0CLM rho U).comp
      (extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r))

/-- The physical regional covariant Laplacian `D_U^{eta*}D_U^eta`. -/
noncomputable def cmp99OmegaSourceCovariantLaplacian
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) :=
  (cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing).adjoint.comp
    (cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing)

/-- Exact regional Dirichlet energy identity. -/
theorem inner_cmp99OmegaSourceCovariantLaplacian
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ)
    (phi : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc)) :
    inner ℝ phi
        (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing phi) =
      ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 := by
  rw [cmp99OmegaSourceCovariantLaplacian,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Self-adjointness of the physical regional covariant Laplacian. -/
theorem cmp99OmegaSourceCovariantLaplacian_isSymmetric
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing).IsSymmetric := by
  let D := cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing
  intro phi psi
  change inner ℝ ((D.adjoint.comp D) phi) psi =
    inner ℝ phi ((D.adjoint.comp D) psi)
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- Uniform source-region bound for the scaled covariant derivative. -/
theorem norm_cmp99OmegaSourceCovariantD0CLM_le
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) :
    ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing‖ ≤
      4 / spacing := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro phi
  have hD := ContinuousLinearMap.le_opNorm (covariantD0CLM rho U)
    (extendZeroZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)
  have hDnorm := norm_covariantD0CLM_le rho U
  have hext := norm_cmp99Omega_extendZeroZeroCLM
    (M := M) Seq r phi
  change ‖spacing⁻¹ • covariantD0CLM rho U
      (extendZeroZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)‖ ≤
    4 / spacing * ‖phi‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspacing)]
  have hnorm4 : ‖covariantD0CLM rho U‖ ≤ 4 := by
    norm_num at hDnorm
    exact hDnorm
  calc
    spacing⁻¹ * ‖covariantD0CLM rho U
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)‖ ≤
      spacing⁻¹ *
        (‖covariantD0CLM rho U‖ * ‖phi‖) :=
      mul_le_mul_of_nonneg_left (by simpa [hext] using hD)
        (inv_nonneg.mpr hspacing.le)
    _ ≤ spacing⁻¹ * (4 * ‖phi‖) := by
      gcongr
    _ = 4 / spacing * ‖phi‖ := by
      field_simp

/-- Uniform source-region upper norm of the covariant Laplacian. -/
theorem norm_cmp99OmegaSourceCovariantLaplacian_le
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) :
    ‖cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing‖ ≤
      16 / spacing ^ 2 := by
  rw [cmp99OmegaSourceCovariantLaplacian,
    ContinuousLinearMap.norm_adjoint_comp_self]
  have hD := norm_cmp99OmegaSourceCovariantD0CLM_le
    Seq r rho U hspacing
  have hnonneg : 0 ≤ 4 / spacing := by positivity
  calc
    ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing‖ *
        ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing‖ ≤
      (4 / spacing) * (4 / spacing) :=
        mul_le_mul hD hD (norm_nonneg _) hnonneg
    _ = 16 / spacing ^ 2 := by
      field_simp
      norm_num

/-- Literal regional source precision on the actual tower field spaces. -/
noncomputable def cmp99OmegaSourcePhysicalGaugePrecision
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (T : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) spacing)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (a : ℝ) :
    CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) :=
  cmp99SourceGaugePrecision
    (cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing) T.Qprime a

/-- The internally generated, volume-independent upper precision constant. -/
noncomputable def cmp99OmegaSourcePhysicalPrecisionUpperBound
    (spacing a : ℝ) : ℝ :=
  16 / spacing ^ 2 + |a|

/-- The physical precision has the printed nonnegative quadratic form. -/
theorem inner_cmp99OmegaSourcePhysicalGaugePrecision
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (T : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) spacing)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (a : ℝ)
    (phi : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc)) :
    inner ℝ phi
        (cmp99OmegaSourcePhysicalGaugePrecision Seq r T rho U a phi) =
      ‖cmp99OmegaSourceCovariantD0CLM Seq r rho U spacing phi‖ ^ 2 +
        a * ‖T.Qprime phi‖ ^ 2 := by
  rw [cmp99OmegaSourcePhysicalGaugePrecision,
    inner_cmp99SourceGaugePrecision,
    inner_cmp99OmegaSourceCovariantLaplacian]

/-- The physical precision is self-adjoint. -/
theorem cmp99OmegaSourcePhysicalGaugePrecision_isSymmetric
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (T : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) spacing)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (a : ℝ) :
    (cmp99OmegaSourcePhysicalGaugePrecision Seq r T rho U a).IsSymmetric :=
  cmp99SourceGaugePrecision_isSymmetric _ _ _
    (cmp99OmegaSourceCovariantLaplacian_isSymmetric Seq r rho U spacing)

/-- Uniform upper norm for the literal physical precision. -/
theorem norm_cmp99OmegaSourcePhysicalGaugePrecision_le
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (T : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) spacing)
    [Nontrivial T.TerminalSpace.carrier]
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a : ℝ} (hspacing : 0 < spacing)
    (hterminal : 0 < T.terminalSpacing)
    (hmono : spacing ≤ T.terminalSpacing) :
    ‖cmp99OmegaSourcePhysicalGaugePrecision Seq r T rho U a‖ ≤
      cmp99OmegaSourcePhysicalPrecisionUpperBound spacing a := by
  have hDelta := norm_cmp99OmegaSourceCovariantLaplacian_le
    Seq r rho U hspacing
  have hQ := T.norm_Qprime_le_one hspacing.le hterminal hmono
  have hmass :
      ‖a • (T.Qprime.adjoint.comp T.Qprime)‖ =
        |a| * ‖T.Qprime‖ ^ 2 := by
    rw [norm_smul, ContinuousLinearMap.norm_adjoint_comp_self,
      Real.norm_eq_abs]
    simp only [pow_two]
  rw [cmp99OmegaSourcePhysicalGaugePrecision, cmp99SourceGaugePrecision]
  calc
    ‖cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing +
        a • (T.Qprime.adjoint.comp T.Qprime)‖ ≤
      ‖cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing‖ +
        ‖a • (T.Qprime.adjoint.comp T.Qprime)‖ := norm_add_le _ _
    _ ≤ 16 / spacing ^ 2 + |a| * ‖T.Qprime‖ ^ 2 := by
      rw [hmass]
      exact add_le_add hDelta le_rfl
    _ ≤ 16 / spacing ^ 2 + |a| := by
      have hQsq : ‖T.Qprime‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg T.Qprime]
      exact add_le_add le_rfl
        (by simpa using mul_le_mul_of_nonneg_left hQsq (abs_nonneg a))
    _ = cmp99OmegaSourcePhysicalPrecisionUpperBound spacing a := rfl

end

end YangMills.RG
