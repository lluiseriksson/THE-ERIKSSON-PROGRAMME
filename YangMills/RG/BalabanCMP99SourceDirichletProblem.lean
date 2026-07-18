/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceBoundaryProblemSpec
import YangMills.RG.BalabanCMP116Eq214Interior
import YangMills.RG.PhysicalGaugeOperator

/-!
# Literal Dirichlet field spaces on the CMP99 source regions

Printed CMP99 defines `Delta'_a | Omega` by Dirichlet boundary conditions:
fields live on `Omega`, are extended by zero outside it, and the ambient
precision is restricted back to the active sites.  This file implements that
construction for every region of `CMP99SourceOmegaGeometry`.

The resulting Green operator is the inverse of the compressed precision on
the *active zero-cochain type*.  No positive mass is added on the ambient
complement, so this is distinct from `cmp99LocalizedPhysicalCovariance`, whose
exterior mass is a useful parametrix device but is not the printed boundary
condition.

The ambient precision is still an explicit input.  Instantiating it with the
literal covariant Laplacian plus `Q'^* a Q'`, and then constructing the printed
`Q' G'^2 Q'^*` covariance, remain the next source-facing steps.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}

/-- Fine-site realization of one source region `Omega_r`: a site is active
exactly when its side-`M` large block belongs to the region. -/
def cmp99OmegaActiveGaugeRegion
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    ActiveGaugeRegion 4 (M * (2 * Q)) where
  sites := cmp116RegionSites (M := M) (N' := 2 * Q) (Seq.regions r)

@[simp] theorem mem_cmp99OmegaActiveGaugeRegion_sites_iff
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (x : FinBox 4 (M * (2 * Q))) :
    x ∈ (cmp99OmegaActiveGaugeRegion (M := M) Seq r).sites ↔
      blockSite M (2 * Q) x ∈ Seq.regions r := by
  exact mem_cmp116RegionSites_iff

/-- The actual admissible zero-cochain space for Dirichlet data on `Omega_r`.
Its type depends on the source region. -/
abbrev CMP99OmegaDirichletZeroField
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (g : Type*) :=
  ActiveGaugeZeroCochain (cmp99OmegaActiveGaugeRegion (M := M) Seq r) g

/-- Restrict an ambient precision after extending the active field by zero.
This is the literal finite-dimensional realization of `Omega Delta'_a Omega`.
-/
noncomputable def cmp99OmegaDirichletZeroPrecision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) :
    CMP99OmegaDirichletZeroField (M := M) Seq r g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r g :=
  (restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).comp
    (K.comp
      (extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)))

/-- Restriction is a left inverse of Dirichlet zero extension. -/
theorem cmp99Omega_restrictZero_extendZero
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    (restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).comp
        (extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq r g) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  have hx : blockSite M (2 * Q) x.1 ∈ Seq.regions r :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq r x.1).mp x.2
  simp [restrictZeroCLM, extendZeroZeroCLM, hx]

/-- The zero extension of an admissible field vanishes at every site whose
large block is outside `Omega_r`. -/
theorem cmp99Omega_extendZero_apply_eq_zero_of_block_not_mem
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (phi : CMP99OmegaDirichletZeroField (M := M) Seq r g)
    (x : FinBox 4 (M * (2 * Q)))
    (hx : blockSite M (2 * Q) x ∉ Seq.regions r) :
    extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi x = 0 := by
  simp [extendZeroZeroCLM, mem_cmp99OmegaActiveGaugeRegion_sites_iff, hx]

/-- The genuine Dirichlet Green operator, generated on the active field space
from coercivity of the compressed precision. -/
noncomputable def cmp99OmegaDirichletZeroGreen
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c) :
    CMP99OmegaDirichletZeroField (M := M) Seq r g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r g :=
  covarianceOfIsCoerciveCLM
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) hc hcoer

/-- `Delta'_a|Omega * G'_Omega = 1` on the active Dirichlet field space. -/
theorem cmp99OmegaDirichletZeroPrecision_comp_green
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c) :
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r).comp
        (cmp99OmegaDirichletZeroGreen (M := M) Seq K r hc hcoer) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq r g) := by
  exact precision_comp_covarianceOfIsCoerciveCLM
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) hc hcoer

/-- `G'_Omega * Delta'_a|Omega = 1` on the active Dirichlet field space. -/
theorem cmp99OmegaDirichletZeroGreen_comp_precision
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c) :
    (cmp99OmegaDirichletZeroGreen (M := M) Seq K r hc hcoer).comp
        (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq r g) := by
  exact covarianceOfIsCoerciveCLM_comp_precision
    (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) hc hcoer

/-- Ambient zero-extension of the genuine Dirichlet Green operator.  This is
the object whose kernels at different source regions can later be compared;
the inverse equations themselves remain on the region-dependent active
spaces above. -/
noncomputable def cmp99OmegaExtendedDirichletZeroGreen
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c) :
    GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g :=
  (extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).comp
    ((cmp99OmegaDirichletZeroGreen (M := M) Seq K r hc hcoer).comp
      (restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)))

/-- The ambient realization of `G'_Omega` still vanishes identically outside
the source region. -/
theorem cmp99OmegaExtendedDirichletZeroGreen_apply_eq_zero_of_block_not_mem
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c)
    (phi : GaugeZeroCochain 4 (M * (2 * Q)) g)
    (x : FinBox 4 (M * (2 * Q)))
    (hx : blockSite M (2 * Q) x ∉ Seq.regions r) :
    cmp99OmegaExtendedDirichletZeroGreen
      (M := M) Seq K r hc hcoer phi x = 0 := by
  exact cmp99Omega_extendZero_apply_eq_zero_of_block_not_mem
    (M := M) Seq r _ x hx

/-- Restricting the ambient realization recovers the active Green output
exactly; no exterior-mass sector is present. -/
theorem cmp99Omega_restrict_comp_extendedDirichletZeroGreen
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j)
    (K : GaugeZeroCochain 4 (M * (2 * Q)) g →L[ℝ]
      GaugeZeroCochain 4 (M * (2 * Q)) g)
    (r : Fin (j + 2)) {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM
      (cmp99OmegaDirichletZeroPrecision (M := M) Seq K r) c) :
    (restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).comp
        (cmp99OmegaExtendedDirichletZeroGreen
          (M := M) Seq K r hc hcoer) =
      (cmp99OmegaDirichletZeroGreen (M := M) Seq K r hc hcoer).comp
        (restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) := by
  apply ContinuousLinearMap.ext
  intro phi
  have h := congrArg
    (fun f => f
      (cmp99OmegaDirichletZeroGreen (M := M) Seq K r hc hcoer
        (restrictZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)))
    (cmp99Omega_restrictZero_extendZero (M := M) (g := g) Seq r)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    cmp99OmegaExtendedDirichletZeroGreen] using h

end

end YangMills.RG
