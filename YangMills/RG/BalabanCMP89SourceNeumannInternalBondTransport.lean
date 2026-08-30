import YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision

/-!
# Exact internal-bond transport from the CMP89 Neumann derivative

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

This leaf isolates the first non-scalar fact needed by the physical Neumann
joint-kernel producer.  Vanishing of the normalized regional derivative,
together with nonzero lattice spacing, gives the literal covariant transport
identity on every retained internal bond.  It does not assume connectivity,
identify a retained average, or prove the joint-kernel theorem.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- A zero CMP89 Neumann derivative makes the field covariantly constant on
each internal positive bond.  The nonzero-spacing premise is explicit: the
normalized derivative carries `spacing⁻¹`, so the conclusion is false at
`spacing = 0`. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_internalBond
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0)
    (b : ActiveGaugeRegion.Bond Omega) :
    phi ⟨b.1.1, (by
      have hb : b.1.1 ∈ Omega.sites ∧
          b.1.1.shift b.1.2 ∈ Omega.sites := by
        simpa [ActiveGaugeRegion.bonds] using b.2
      exact hb.1)⟩ =
      rho.adCLM (U (ConcreteEdge.mk b.1.1 b.1.2 true))
        (phi ⟨b.1.1.shift b.1.2, (by
          have hb : b.1.1 ∈ Omega.sites ∧
              b.1.1.shift b.1.2 ∈ Omega.sites := by
            simpa [ActiveGaugeRegion.bonds] using b.2
          exact hb.2)⟩) := by
  rcases b with ⟨⟨x, i⟩, hb⟩
  have hb' : x ∈ Omega.sites ∧ x.shift i ∈ Omega.sites := by
    simpa [ActiveGaugeRegion.bonds] using hb
  have hx : x ∈ Omega.sites := hb'.1
  have hy : x.shift i ∈ Omega.sites := hb'.2
  have hAt := congrArg
    (fun A : ActiveGaugeOneCochain Omega (SUNLieCoord Nc) =>
      A ⟨(x, i), hb⟩) hD
  have hscaled :
      spacing⁻¹ •
          (phi ⟨x, hx⟩ -
            rho.adCLM (U (ConcreteEdge.mk x i true))
              (phi ⟨x.shift i, hy⟩)) = 0 := by
    simpa [cmp89SourceNeumannRegionalCovariantD0CLM,
      restrictOneCLM, covariantD0CLM_apply, extendZeroZeroCLM, hx, hy]
      using hAt
  have hdefect :
      phi ⟨x, hx⟩ -
          rho.adCLM (U (ConcreteEdge.mk x i true))
            (phi ⟨x.shift i, hy⟩) = 0 := by
    exact (smul_eq_zero.mp hscaled).resolve_left (inv_ne_zero hspacing)
  exact sub_eq_zero.mp hdefect

end

end YangMills.RG
