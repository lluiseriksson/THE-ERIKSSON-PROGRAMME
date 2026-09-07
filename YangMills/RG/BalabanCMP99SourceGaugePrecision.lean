/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceDirichletProblem
import YangMills.RG.GaugePrecision

/-!
# CMP99 source precision `Delta'_a = Delta_U + Q'^* a Q'`

This file fixes the operator algebra printed in CMP99 before constructing the
model-specific covariant Laplacian and multiscale averaging map.  The
adjoint-mass term has the exact nonnegative quadratic form

`a * ||Q' phi||^2`.

Consequently any ambient coercivity constant for `Delta_U` is inherited by
`Delta'_a`, and the literal Dirichlet compression on every source region
inherits the same constant by zero-extension isometry.  This removes the
independent per-region `hcoer` premise from the Green construction.

`Qprime` remains an explicit operator input: this module does not identify an
arbitrary map with Balaban's recursive covariant average.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- Literal source operator `Delta'_a = Delta_U + a Q'^* Q'`. -/
def cmp99SourceGaugePrecision
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (covariantLaplacian : E →L[ℝ] E) (Qprime : E →L[ℝ] F)
    (a : ℝ) : E →L[ℝ] E :=
  covariantLaplacian + a • (Qprime.adjoint.comp Qprime)

/-- Exact quadratic form of the printed adjoint-mass precision. -/
theorem inner_cmp99SourceGaugePrecision
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (covariantLaplacian : E →L[ℝ] E) (Qprime : E →L[ℝ] F)
    (a : ℝ) (phi : E) :
    inner ℝ phi
        (cmp99SourceGaugePrecision covariantLaplacian Qprime a phi) =
      inner ℝ phi (covariantLaplacian phi) + a * ‖Qprime phi‖ ^ 2 := by
  rw [cmp99SourceGaugePrecision, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- A nonnegative `Q'^* a Q'` term preserves any ambient coercivity constant
of the covariant Laplacian. -/
theorem isCoerciveCLM_cmp99SourceGaugePrecision
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (covariantLaplacian : E →L[ℝ] E) (Qprime : E →L[ℝ] F)
    {a c : ℝ} (ha : 0 ≤ a)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    IsCoerciveCLM
      (cmp99SourceGaugePrecision covariantLaplacian Qprime a) c := by
  intro phi
  rw [inner_cmp99SourceGaugePrecision]
  exact (hDelta phi).trans (le_add_of_nonneg_right
    (mul_nonneg ha (sq_nonneg ‖Qprime phi‖)))

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}

/-- The same ambient constant descends to every source-region compression of
the literal `Delta'_a`. -/
theorem isCoerciveCLM_cmp99OmegaDirichletSourceGaugePrecision
    {g F : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (covariantLaplacian :
      GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
        GaugeZeroCochain 4 (M * (2 * Q)) g)
    (Qprime : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ] F)
    (r : Fin (j + 2)) {a c : ℝ} (ha : 0 ≤ a)
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq
        (cmp99SourceGaugePrecision covariantLaplacian Qprime a) r) c :=
  isCoerciveCLM_cmp99OmegaDirichletZeroPrecision (M := M) Seq _ r
    (isCoerciveCLM_cmp99SourceGaugePrecision
      covariantLaplacian Qprime ha hDelta)

/-- Source Green operator generated directly from ambient coercivity of
`Delta_U` and nonnegativity of the printed adjoint mass. -/
noncomputable def cmp99OmegaSourceGaugeDirichletGreen
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
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    CMP99OmegaDirichletZeroField (M := M) Seq r g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r g :=
  cmp99OmegaDirichletZeroGreen (M := M) Seq
    (cmp99SourceGaugePrecision covariantLaplacian Qprime a) r hc
    (isCoerciveCLM_cmp99OmegaDirichletSourceGaugePrecision
      (M := M) Seq covariantLaplacian Qprime r ha hDelta)

/-- Both source ingredients now generate the left inverse equation without a
region-specific coercivity binder. -/
theorem cmp99OmegaSourceGaugePrecision_comp_green
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
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq
      (cmp99SourceGaugePrecision covariantLaplacian Qprime a) r).comp
        (cmp99OmegaSourceGaugeDirichletGreen
          (M := M) Seq covariantLaplacian Qprime r ha hc hDelta) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq r g) := by
  exact cmp99OmegaDirichletZeroPrecision_comp_green (M := M) Seq _ r hc
    (isCoerciveCLM_cmp99OmegaDirichletSourceGaugePrecision
      (M := M) Seq covariantLaplacian Qprime r ha hDelta)

/-- Right inverse equation for the same source-generated Green operator. -/
theorem cmp99OmegaSourceGaugeGreen_comp_precision
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
    (hDelta : IsCoerciveCLM covariantLaplacian c) :
    (cmp99OmegaSourceGaugeDirichletGreen
      (M := M) Seq covariantLaplacian Qprime r ha hc hDelta).comp
        (cmp99OmegaDirichletZeroPrecision (M := M) Seq
          (cmp99SourceGaugePrecision covariantLaplacian Qprime a) r) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq r g) := by
  exact cmp99OmegaDirichletZeroGreen_comp_precision (M := M) Seq _ r hc
    (isCoerciveCLM_cmp99OmegaDirichletSourceGaugePrecision
      (M := M) Seq covariantLaplacian Qprime r ha hDelta)

end

end YangMills.RG
