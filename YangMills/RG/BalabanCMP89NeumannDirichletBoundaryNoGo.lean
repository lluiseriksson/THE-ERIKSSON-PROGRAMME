import YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision

/-!
# CMP89 Neumann versus zero-extension Dirichlet: boundary no-go

CMP89's regional Neumann derivative retains only bonds whose two endpoints
belong to the source rectangle.  The existing retained CMP99 derivative first
extends a site field by zero and then evaluates the ambient derivative on all
bonds.  On a bond leaving a proper region these conventions differ
definitionally: the extended Neumann derivative is zero, whereas the
zero-extension Dirichlet derivative reads the nonzero value at the interior
endpoint.

This module seals that mismatch at the derivative level.  It does not claim a
comparison of the two Laplacian norms or Green functions, and it does not
construct the source rectangle required by CMP89 (2.42).
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- A boundary-crossing bond is killed after extending the internal-bond
Neumann derivative back to the ambient one-cochain carrier. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_boundary_eq_zero
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : FinBox d N) (i : Fin d)
    (hx : x ∈ Omega.sites) (hy : x.shift i ∉ Omega.sites) :
    extendZeroOneCLM Omega
        (cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi) (x, i) = 0 := by
  have hb : (x, i) ∉ Omega.bonds := by
    simp [ActiveGaugeRegion.bonds, hx, hy]
  simp [extendZeroOneCLM, hb]

/-- At the trivial background, the zero-extension Dirichlet derivative on
the same boundary-crossing bond is the scaled interior endpoint value. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_boundary_eq
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : FinBox d N) (i : Fin d)
    (hx : x ∈ Omega.sites) (hy : x.shift i ∉ Omega.sites) :
    cmp99ActiveRegionSourceCovariantD0CLM Omega rho
        (trivialPhysicalGaugeBackground d N Nc) spacing phi (x, i) =
      spacing⁻¹ • phi ⟨x, hx⟩ := by
  simp [cmp99ActiveRegionSourceCovariantD0CLM,
    covariantD0CLM_apply,
    extendZeroZeroCLM_apply_of_mem Omega phi x hx,
    extendZeroZeroCLM_apply_of_not_mem Omega phi (x.shift i) hy,
    trivialPhysicalGaugeBackground, SUNAdjointModel.ad_one_apply]

/-- The source Neumann derivative and the zero-extension Dirichlet derivative
cannot be identified when a nonzero field meets a boundary-crossing bond. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_ne_dirichlet_of_boundary
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : FinBox d N) (i : Fin d)
    (hx : x ∈ Omega.sites) (hy : x.shift i ∉ Omega.sites)
    (hphi : phi ⟨x, hx⟩ ≠ 0) :
    extendZeroOneCLM Omega
        (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho
          (trivialPhysicalGaugeBackground d N Nc) spacing phi) ≠
      cmp99ActiveRegionSourceCovariantD0CLM Omega rho
        (trivialPhysicalGaugeBackground d N Nc) spacing phi := by
  intro hEq
  have hAt := congrArg (fun A => A (x, i)) hEq
  change
    extendZeroOneCLM Omega
        (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho
          (trivialPhysicalGaugeBackground d N Nc) spacing phi) (x, i) =
      cmp99ActiveRegionSourceCovariantD0CLM Omega rho
        (trivialPhysicalGaugeBackground d N Nc) spacing phi (x, i) at hAt
  rw [cmp89SourceNeumannRegionalCovariantD0CLM_boundary_eq_zero
        Omega rho (trivialPhysicalGaugeBackground d N Nc) spacing phi
        x i hx hy,
      cmp99ActiveRegionSourceCovariantD0CLM_boundary_eq
        Omega rho spacing phi x i hx hy] at hAt
  exact (smul_ne_zero (inv_ne_zero hspacing) hphi) hAt.symm

end

end YangMills.RG
