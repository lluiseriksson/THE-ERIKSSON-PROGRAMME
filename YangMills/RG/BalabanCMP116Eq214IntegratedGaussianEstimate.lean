/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214FiniteGaussianData
import YangMills.RG.BalabanCMP116Eq214CauchyEstimate
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# CMP116 equation (2.14): bounds after the inner Gaussian integration

The bilinear factor `exp (-<B, Gamma X>)` in the literal source integrand is
not uniformly bounded as a function of `B`.  CMP116 instead combines it with
the conditioned Gaussian and evaluates that integral in equations
(2.23)--(2.25).  This module records the physically usable estimate: a bound
on the already integrated inner Gaussian is propagated through the outer
probability integral and the nested Cauchy contours.

It also proves a genuine source-factor estimate: the real positive-semidefinite
quadratic weight appearing in the outer `X` integral is a contraction.
-/

namespace YangMills.RG

open MeasureTheory Matrix

/-- Finite-coordinate version of the outer factor
`z exp (-1/2 <X, A X>)` in CMP116 equation (2.14). -/
noncomputable def cmp116Eq214OuterQuadraticWeight
    {ι : Type*} [Fintype ι]
    (z : ℂ) (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℂ :=
  z * Complex.exp (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2))

/-- A nonnegative real quadratic form makes the outer exponential a
contraction. -/
theorem norm_cmp116Eq214OuterQuadraticWeight_le
    {ι : Type*} [Fintype ι]
    (z : ℂ) (A : Matrix ι ι ℝ) (x : ι → ℝ)
    (hquad : 0 ≤ x ⬝ᵥ (A *ᵥ x)) :
    ‖cmp116Eq214OuterQuadraticWeight z A x‖ ≤ ‖z‖ := by
  rw [cmp116Eq214OuterQuadraticWeight, norm_mul, Complex.norm_exp]
  have hre :
      (-(((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) / 2)).re =
        -(x ⬝ᵥ (A *ᵥ x)) / 2 := by
    norm_num
    ring
  rw [hre]
  have hexp : Real.exp (-(x ⬝ᵥ (A *ᵥ x)) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  simpa using mul_le_mul_of_nonneg_left hexp (norm_nonneg z)

/-- Positive semidefiniteness is the source-facing sufficient condition for
the quadratic contraction. -/
theorem norm_cmp116Eq214OuterQuadraticWeight_le_of_posSemidef
    {ι : Type*} [Fintype ι]
    (z : ℂ) (A : Matrix ι ι ℝ) (x : ι → ℝ)
    (hA : A.PosSemidef) :
    ‖cmp116Eq214OuterQuadraticWeight z A x‖ ≤ ‖z‖ := by
  apply norm_cmp116Eq214OuterQuadraticWeight_le z A x
  simpa using hA.dotProduct_mulVec_nonneg x

/-- Propagate a uniform estimate for the *evaluated inner Gaussian integral*
through the outer probability integral.  Unlike a pointwise `innerWeight`
bound, this premise is satisfiable for the bilinear Gaussian factor in (2.14). -/
theorem CMP116Eq214AnalyticData.norm_analyticIntegrand_le_of_innerGaussianIntegral
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (houter_nonneg : 0 ≤ outerBound)
    (hmu0 : IsProbabilityMeasure A.mu0)
    (houter : ∀ x,
      ‖A.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinnerGaussian : ∀ x,
      ‖∫ b, A.innerIntegrand Y0 P sigma tau psi phi x b
          ∂A.conditionedMeasure sigma tau‖ ≤ innerGaussianBound) :
    ‖A.analyticIntegrand Y0 P sigma tau psi phi‖ ≤
      outerBound * innerGaussianBound := by
  letI : IsProbabilityMeasure A.mu0 := hmu0
  unfold CMP116Eq214AnalyticData.analyticIntegrand
  simpa using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := A.mu0)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul (houter x) (hinnerGaussian x)
          (norm_nonneg _) houter_nonneg))

/-- Uniform evaluated-inner-Gaussian estimates imply the complete nested
Cauchy boundary condition, without any impossible pointwise bound on the
bilinear exponential. -/
theorem CMP116Eq214AnalyticData.nestedCauchyBoundaryBound_of_innerGaussianIntegral
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (houter_nonneg : 0 ≤ outerBound)
    (hmu0 : IsProbabilityMeasure A.mu0)
    (houter : ∀ sigma tau x,
      ‖A.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinnerGaussian : ∀ sigma tau x,
      ‖∫ b, A.innerIntegrand Y0 P sigma tau psi phi x b
          ∂A.conditionedMeasure sigma tau‖ ≤ innerGaussianBound) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      A.deltaRadius A.yRadius
      (fun sigma tau => A.analyticIntegrand Y0 P sigma tau psi phi)
      (outerBound * innerGaussianBound) := by
  apply cmp116Eq214NestedCauchyBoundaryBound_of_forall_norm_le
  intro sigma tau
  exact A.norm_analyticIntegrand_le_of_innerGaussianIntegral
    Y0 P sigma tau psi phi outerBound innerGaussianBound
    houter_nonneg hmu0 (houter sigma tau)
    (hinnerGaussian sigma tau)

/-- Finite-Gaussian specialization of the integrated-inner route.  The outer
measure is normalized by construction, while the conditioned Gaussian is
consumed inside the supplied evaluated integral estimate. -/
theorem CMP116Eq214FiniteGaussianData.nestedCauchyBoundaryBound_of_innerGaussianIntegral
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinnerGaussian : ∀ sigma tau x,
      ‖∫ b, G.toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b
          ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
        innerGaussianBound) :
    CMP116Eq214NestedCauchyBoundaryBound nDelta nY
      G.deltaRadius G.yRadius
      (fun sigma tau =>
        G.toAnalyticData.analyticIntegrand Y0 P sigma tau psi phi)
      (outerBound * innerGaussianBound) := by
  exact G.toAnalyticData.nestedCauchyBoundaryBound_of_innerGaussianIntegral
    Y0 P psi phi outerBound innerGaussianBound houter_nonneg
    G.toAnalyticData_mu0_isProbability houter hinnerGaussian

/-- The evaluated-inner-Gaussian estimate feeds the quantitative Cauchy
majorant for one literal equation-(2.14) term. -/
theorem CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_innerGaussianIntegral
    {nDelta nY lieDim : ℕ} {Bond Ψ Φ E : Type*}
    [Fintype Bond] [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY Bond Ψ Φ E lieDim)
    (Y0 P : Finset Bond) (psi : Ψ) (phi : Φ)
    (outerBound innerGaussianBound : ℝ)
    (hDelta : ∀ i, 0 < G.deltaRadius i)
    (hY : ∀ i, 0 < G.yRadius i)
    (houter_nonneg : 0 ≤ outerBound)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinnerGaussian : ∀ sigma tau x,
      ‖∫ b, G.toAnalyticData.innerIntegrand
          Y0 P sigma tau psi phi x b
          ∂G.toAnalyticData.conditionedMeasure sigma tau‖ ≤
        innerGaussianBound) :
    ‖G.toAnalyticData.term Y0 P psi phi‖ ≤
      cmp116Eq214CauchyRate nDelta G.deltaRadius
        (cmp116Eq214CauchyRate nY G.yRadius
          (outerBound * innerGaussianBound)) := by
  exact G.toAnalyticData.norm_term_le_cauchyRate
    Y0 P psi phi (outerBound * innerGaussianBound) hDelta hY
    (G.nestedCauchyBoundaryBound_of_innerGaussianIntegral
      Y0 P psi phi outerBound innerGaussianBound houter_nonneg
      houter hinnerGaussian)

end YangMills.RG
