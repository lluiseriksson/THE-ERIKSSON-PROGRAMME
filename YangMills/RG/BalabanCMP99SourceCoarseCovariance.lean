/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGaugePrecision

/-!
# The CMP99 middle operator `Q'_r G'_r^2 Q'^*_r`

This file closes the source-independent Hilbert-space layer between the
literal Dirichlet Green operator and the printed coarse covariance.  It proves
self-adjointness of the precision and its inverse, constructs the regional
average by zero extension, and identifies the quadratic form of

`Q'_r G'_r^2 Q'^*_r`

with `||G'_r Q'^*_r eta||^2`.

The resulting coercivity theorem exposes exactly the two quantitative inputs
that a physical recursive average must later provide: a uniform upper bound
`Lambda` for the regional precision and a lower bound `q` for the regional
adjoint average.  No such lower bound is claimed here.

In particular, the codomain `F` below is still explicit.  For a proper source
region a positive lower bound on a global coarse codomain is generally false:
coarse data supported outside the region are killed by the regional adjoint.
The source-faithful instantiation must therefore construct a region-dependent
coarse field space together with Balaban's recursive covariant average `Q'`.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- The adjoint mass preserves symmetry of a symmetric ambient precision. -/
theorem cmp99SourceGaugePrecision_isSymmetric
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (covariantLaplacian : E →L[ℝ] E) (Qprime : E →L[ℝ] F)
    (a : ℝ) (hDelta : covariantLaplacian.IsSymmetric) :
    (cmp99SourceGaugePrecision covariantLaplacian Qprime a).IsSymmetric := by
  let A := cmp99SourceGaugePrecision covariantLaplacian Qprime a
  have hAdj : A.adjoint = A := by
    simp [A, cmp99SourceGaugePrecision, hDelta.clm_adjoint_eq]
  exact (ContinuousLinearMap.eq_adjoint_iff A A).mp hAdj.symm

/-- Adjoint form of symmetry for the literal source precision. -/
theorem cmp99SourceGaugePrecision_adjoint_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (covariantLaplacian : E →L[ℝ] E) (Qprime : E →L[ℝ] F)
    (a : ℝ) (hDelta : covariantLaplacian.IsSymmetric) :
    (cmp99SourceGaugePrecision covariantLaplacian Qprime a).adjoint =
      cmp99SourceGaugePrecision covariantLaplacian Qprime a :=
  (cmp99SourceGaugePrecision_isSymmetric
    covariantLaplacian Qprime a hDelta).clm_adjoint_eq

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}

/-- A symmetric ambient operator has a symmetric literal Dirichlet
compression. -/
theorem cmp99OmegaDirichletZeroPrecision_isSymmetric
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) (hK : K.IsSymmetric) :
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r).IsSymmetric := by
  intro phi psi
  let Ezero :
      CMP99OmegaDirichletZeroField (M := M) Seq r g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g :=
    extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
  have hphi := inner_cmp99Omega_restrictZero_eq_extendZero
    (M := M) (g := g) Seq r phi (K (Ezero psi))
  have hpsi := inner_cmp99Omega_restrictZero_eq_extendZero
    (M := M) (g := g) Seq r psi (K (Ezero phi))
  have hKpsiPhi :
      inner ℝ (K (Ezero psi)) (Ezero phi) =
        inner ℝ (Ezero psi) (K (Ezero phi)) := by
    exact hK (Ezero psi) (Ezero phi)
  change inner ℝ
      ((restrictZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
          (K (Ezero phi))) psi =
    inner ℝ phi
      ((restrictZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
          (K (Ezero psi)))
  calc
    inner ℝ
        ((restrictZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
            (K (Ezero phi))) psi =
        inner ℝ psi
          ((restrictZeroCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
              (K (Ezero phi))) := real_inner_comm _ _
    _ = inner ℝ (Ezero psi) (K (Ezero phi)) := hpsi
    _ = inner ℝ (K (Ezero psi)) (Ezero phi) := by
      exact hKpsiPhi.symm
    _ = inner ℝ (Ezero phi) (K (Ezero psi)) := real_inner_comm _ _
    _ = inner ℝ phi
        ((restrictZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
            (K (Ezero psi))) := hphi.symm

/-- Adjoint form of symmetry for every regional compression. -/
theorem cmp99OmegaDirichletZeroPrecision_adjoint_eq
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) (hK : K.IsSymmetric) :
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r).adjoint =
      cmp99OmegaDirichletZeroPrecision (M := M) Seq K r :=
  (cmp99OmegaDirichletZeroPrecision_isSymmetric
    (M := M) Seq K r hK).clm_adjoint_eq

/-- The exact inverse of a symmetric strictly coercive precision is
symmetric.  The proof uses only the two inverse equations. -/
theorem covarianceOfIsCoerciveCLM_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceOfIsCoerciveCLM A hc hA).IsSymmetric := by
  intro x y
  let G := covarianceOfIsCoerciveCLM A hc hA
  have hx : A (G x) = x :=
    precision_apply_covarianceOfIsCoerciveCLM A hc hA x
  have hy : A (G y) = y :=
    precision_apply_covarianceOfIsCoerciveCLM A hc hA y
  calc
    inner ℝ (G x) y = inner ℝ (G x) (A (G y)) := by rw [hy]
    _ = inner ℝ (A (G x)) (G y) := (hSymm (G x) (G y)).symm
    _ = inner ℝ x (G y) := by rw [hx]

/-- Adjoint form of the preceding inverse-symmetry theorem. -/
theorem covarianceOfIsCoerciveCLM_adjoint_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric) :
    (covarianceOfIsCoerciveCLM A hc hA).adjoint =
      covarianceOfIsCoerciveCLM A hc hA :=
  (covarianceOfIsCoerciveCLM_isSymmetric A hc hA hSymm).clm_adjoint_eq

/-- The source-generated regional Green is symmetric whenever the ambient
covariant Laplacian is symmetric. -/
theorem cmp99OmegaSourceGaugeDirichletGreen_isSymmetric
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric) :
    (cmp99OmegaSourceGaugeDirichletGreen
      (M := M) Seq covariantLaplacian Qprime r ha hc hDelta).IsSymmetric := by
  unfold cmp99OmegaSourceGaugeDirichletGreen cmp99OmegaDirichletZeroGreen
  exact covarianceOfIsCoerciveCLM_isSymmetric _ hc
    (isCoerciveCLM_cmp99OmegaDirichletSourceGaugePrecision
      (M := M) Seq covariantLaplacian Qprime r ha hDelta)
    (cmp99OmegaDirichletZeroPrecision_isSymmetric (M := M) Seq _ r
      (cmp99SourceGaugePrecision_isSymmetric
        covariantLaplacian Qprime a hDeltaSymm))

/-- Adjoint form of symmetry for the same regional Green. -/
theorem cmp99OmegaSourceGaugeDirichletGreen_adjoint_eq
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric) :
    (cmp99OmegaSourceGaugeDirichletGreen
      (M := M) Seq covariantLaplacian Qprime r ha hc hDelta).adjoint =
      cmp99OmegaSourceGaugeDirichletGreen
        (M := M) Seq covariantLaplacian Qprime r ha hc hDelta :=
  (cmp99OmegaSourceGaugeDirichletGreen_isSymmetric
    (M := M) Seq covariantLaplacian Qprime r ha hc hDelta
      hDeltaSymm).clm_adjoint_eq

/-- Regional realization of an explicit ambient average: extend the active
field by zero and then apply the ambient map. -/
noncomputable def cmp99OmegaSourceRegionalAverage
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) :
    CMP99OmegaDirichletZeroField (M := M) Seq r g →L[ℝ] F :=
  Qprime.comp
    (extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r))

/-- Abstract middle operator with the actual Hilbert adjoint, rather than an
independent `QprimeStar` input. -/
noncomputable def cmp99SourceCoarseCovarianceMiddle
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Qregional : E →L[ℝ] F) (G : E →L[ℝ] E) : F →L[ℝ] F :=
  Qregional.comp (G.comp (G.comp Qregional.adjoint))

/-- The literal regional source middle operator, still parameterized by the
ambient average whose source-faithful construction remains open. -/
noncomputable def cmp99OmegaSourceGaugeCoarseCovarianceMiddle
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c) : F →L[ℝ] F :=
  cmp99SourceCoarseCovarianceMiddle
    (cmp99OmegaSourceRegionalAverage (M := M) Seq Qprime r)
    (cmp99OmegaSourceGaugeDirichletGreen
      (M := M) Seq covariantLaplacian Qprime r ha hc hDelta)

/-- Exact square identity for the printed middle operator. -/
theorem inner_cmp99SourceCoarseCovarianceMiddle
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Qregional : E →L[ℝ] F) (G : E →L[ℝ] E)
    (hG : G.IsSymmetric) (eta : F) :
    inner ℝ eta (cmp99SourceCoarseCovarianceMiddle Qregional G eta) =
      ‖G (Qregional.adjoint eta)‖ ^ 2 := by
  rw [cmp99SourceCoarseCovarianceMiddle]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℝ (Qregional.adjoint eta)
        (G (G (Qregional.adjoint eta))) =
      inner ℝ (G (Qregional.adjoint eta))
        (G (Qregional.adjoint eta)) :=
      (hG (Qregional.adjoint eta) (G (Qregional.adjoint eta))).symm
    _ = ‖G (Qregional.adjoint eta)‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Source-specialized square identity for the regional middle operator. -/
theorem inner_cmp99OmegaSourceGaugeCoarseCovarianceMiddle
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hDelta : IsCoerciveCLM covariantLaplacian c)
    (hDeltaSymm : covariantLaplacian.IsSymmetric) (eta : F) :
    inner ℝ eta
        (cmp99OmegaSourceGaugeCoarseCovarianceMiddle
          (M := M) Seq covariantLaplacian Qprime r ha hc hDelta eta) =
      ‖cmp99OmegaSourceGaugeDirichletGreen
          (M := M) Seq covariantLaplacian Qprime r ha hc hDelta
        ((cmp99OmegaSourceRegionalAverage
          (M := M) Seq Qprime r).adjoint eta)‖ ^ 2 := by
  exact inner_cmp99SourceCoarseCovarianceMiddle _ _
    (cmp99OmegaSourceGaugeDirichletGreen_isSymmetric
      (M := M) Seq covariantLaplacian Qprime r ha hc hDelta hDeltaSymm) eta

/-- An upper norm bound on an invertible precision gives the lower estimate
needed for its Green operator. -/
theorem norm_le_mul_norm_covarianceOfIsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {c Lambda : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hLambda : ‖A‖ ≤ Lambda) (y : E) :
    ‖y‖ ≤ Lambda * ‖covarianceOfIsCoerciveCLM A hc hA y‖ := by
  let G := covarianceOfIsCoerciveCLM A hc hA
  have hy : A (G y) = y :=
    precision_apply_covarianceOfIsCoerciveCLM A hc hA y
  calc
    ‖y‖ = ‖A (G y)‖ := by rw [hy]
    _ ≤ ‖A‖ * ‖G y‖ := ContinuousLinearMap.le_opNorm A (G y)
    _ ≤ Lambda * ‖G y‖ :=
      mul_le_mul_of_nonneg_right hLambda (norm_nonneg (G y))

/-- Coercivity of `Q G^2 Q^*` from an explicit precision upper bound and an
explicit lower bound for the regional adjoint average. -/
theorem isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →L[ℝ] E) (Qregional : E →L[ℝ] F)
    {c q Lambda : ℝ} (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hq : 0 ≤ q) (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda)
    (hQlower : ∀ eta : F, q * ‖eta‖ ≤ ‖Qregional.adjoint eta‖) :
    IsCoerciveCLM
      (cmp99SourceCoarseCovarianceMiddle Qregional
        (covarianceOfIsCoerciveCLM A hc hA)) ((q / Lambda) ^ 2) := by
  intro eta
  let G := covarianceOfIsCoerciveCLM A hc hA
  have hGsymm : G.IsSymmetric :=
    covarianceOfIsCoerciveCLM_isSymmetric A hc hA hSymm
  have hinverse := norm_le_mul_norm_covarianceOfIsCoerciveCLM
    A hc hA hLambda (Qregional.adjoint eta)
  have hlower : (q / Lambda) * ‖eta‖ ≤ ‖G (Qregional.adjoint eta)‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLambdaPos).2
    calc
      q * ‖eta‖ ≤ ‖Qregional.adjoint eta‖ := hQlower eta
      _ ≤ Lambda * ‖G (Qregional.adjoint eta)‖ := hinverse
      _ = ‖G (Qregional.adjoint eta)‖ * Lambda := mul_comm _ _
  rw [inner_cmp99SourceCoarseCovarianceMiddle Qregional G hGsymm eta]
  have hnonneg : 0 ≤ (q / Lambda) * ‖eta‖ :=
    mul_nonneg (div_nonneg hq hLambdaPos.le) (norm_nonneg eta)
  calc
    (q / Lambda) ^ 2 * ‖eta‖ ^ 2 =
        ((q / Lambda) * ‖eta‖) ^ 2 := by ring
    _ ≤ ‖G (Qregional.adjoint eta)‖ ^ 2 :=
      pow_le_pow_left₀ hnonneg hlower 2

/-- Once the preceding middle operator is strictly coercive, its inverse is
the printed regional coarse covariance. -/
noncomputable def cmp99SourceCoarseCovariance
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →L[ℝ] E) (Qregional : E →L[ℝ] F)
    {c q Lambda : ℝ} (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hqPos : 0 < q) (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda)
    (hQlower : ∀ eta : F, q * ‖eta‖ ≤ ‖Qregional.adjoint eta‖) :
    F →L[ℝ] F :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceCoarseCovarianceMiddle Qregional
      (covarianceOfIsCoerciveCLM A hc hA))
    (sq_pos_of_pos (div_pos hqPos hLambdaPos))
    (isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle
      A Qregional hc hLambdaPos hqPos.le hA hSymm hLambda hQlower)

/-- The generated coarse covariance is a left inverse of the middle
operator. -/
theorem cmp99SourceCoarseCovariance_comp_middle
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →L[ℝ] E) (Qregional : E →L[ℝ] F)
    {c q Lambda : ℝ} (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hqPos : 0 < q) (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda)
    (hQlower : ∀ eta : F, q * ‖eta‖ ≤ ‖Qregional.adjoint eta‖) :
    (cmp99SourceCoarseCovariance A Qregional hc hLambdaPos hqPos hA
      hSymm hLambda hQlower).comp
        (cmp99SourceCoarseCovarianceMiddle Qregional
          (covarianceOfIsCoerciveCLM A hc hA)) =
      ContinuousLinearMap.id ℝ F := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (sq_pos_of_pos (div_pos hqPos hLambdaPos))
    (isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle A Qregional hc
      hLambdaPos hqPos.le hA hSymm hLambda hQlower)

/-- The generated coarse covariance is also a right inverse. -/
theorem cmp99SourceCoarseCovariance_middle_comp
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →L[ℝ] E) (Qregional : E →L[ℝ] F)
    {c q Lambda : ℝ} (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hqPos : 0 < q) (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda)
    (hQlower : ∀ eta : F, q * ‖eta‖ ≤ ‖Qregional.adjoint eta‖) :
    (cmp99SourceCoarseCovarianceMiddle Qregional
      (covarianceOfIsCoerciveCLM A hc hA)).comp
        (cmp99SourceCoarseCovariance A Qregional hc hLambdaPos hqPos hA
          hSymm hLambda hQlower) =
      ContinuousLinearMap.id ℝ F := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (sq_pos_of_pos (div_pos hqPos hLambdaPos))
    (isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle A Qregional hc
      hLambdaPos hqPos.le hA hSymm hLambda hQlower)

end

end YangMills.RG
