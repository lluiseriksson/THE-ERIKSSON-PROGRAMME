import YangMills.RG.BalabanCMP89SourceNeumannPathTransport
import YangMills.RG.BalabanCMP99CoarseDerivativeDecomposition

/-!
# The straight CMP99 defect vanishes on the CMP89 Neumann kernel

For an internal coarse bond, the literal length-`M` fine path stays in the
union of the two complete endpoint blocks. Hence a field in the regional
Neumann kernel transports exactly along that path, and the straight defect
in the CMP99 coarse-derivative decomposition is zero.

This brick does not set the full coarse derivative to zero: the explicit
`Ubar` transport remainder remains. That remainder is the quantitative
input for the recursive Neumann absorption argument.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Endpoint membership for the positive physical coordinate of every edge
is equivalent to path containment. The reverse orientation swaps the two
members explicitly. -/
theorem OrientedLatticePath.staysIn_of_physicalBondEndpointsIn
    {G : Type*} [Group G]
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := G) a b}
    {S : Finset (FinBox d (M * N'))}
    (hends : ∀ e ∈ Gamma.edges,
      CMP99PhysicalBondEndpointsIn S (physicalBondOfEdge e)) :
    Gamma.StaysIn S := by
  intro e he
  have h := hends e he
  rcases e with ⟨x, i, sign⟩
  cases sign with
  | false =>
      simpa only [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
        ConcreteEdge.srcV, ConcreteEdge.dstV] using And.intro h.2 h.1
  | true =>
      simpa only [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
        ConcreteEdge.srcV, ConcreteEdge.dstV] using h

/-- If both endpoint blocks are active, every edge of the printed straight
fine path is an internal regional bond. -/
theorem cmp99SourceParallelTransportPath_staysIn_of_coarseEndpoints
    (Omega : ActiveGaugeRegion d (M * N'))
    (y : FinBox d N') (mu : Fin d)
    (hy : y ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (hy' : y.shift mu ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' y) :
    (cmp99SourceParallelTransportPath (G := SUN Nc) x mu).StaysIn
      Omega.sites := by
  apply OrientedLatticePath.staysIn_of_physicalBondEndpointsIn
  intro e he
  have hsource : blockOf M N' y ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega y).mp hy
  have htarget : blockOf M N' (y.shift mu) ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega (y.shift mu)).mp hy'
  exact CMP99PhysicalBondEndpointsIn.mono
    (Finset.union_subset hsource htarget)
    (cmp99SourceParallelTransportPath_endpointsIn_twoBlocks
      y x mu hx e he)

/-- On an internal coarse bond, the exact straight component of the coarse
derivative vanishes for a fine field in the regional Neumann kernel. -/
theorem cmp99SourceParallelAverageDefectValue_extendZero_eq_zero
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0)
    (y : FinBox d N') (mu : Fin d)
    (hy : y ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (hy' : y.shift mu ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites) :
    cmp99SourceParallelAverageDefectValue rho U
      (extendZeroZeroCLM Omega phi) y mu = 0 := by
  unfold cmp99SourceParallelAverageDefectValue
  rw [Finset.sum_eq_zero]
  · exact smul_zero _
  · intro x _hx
    have hsource : blockOf M N' y ⊆ Omega.sites :=
      (mem_cmp99ActiveCoarseRegion_sites_iff Omega y).mp hy
    have htarget : blockOf M N' (y.shift mu) ⊆ Omega.sites :=
      (mem_cmp99ActiveCoarseRegion_sites_iff Omega (y.shift mu)).mp hy'
    have hxOmega : x.1 ∈ Omega.sites := hsource x.2
    have hxTargetBlock :=
      cmp99SourceTranslatedSite_mem_targetBlock y mu x.1 x.2
    have hxTarget : cmp99SourceTranslatedSite x.1 mu ∈ Omega.sites :=
      htarget hxTargetBlock
    have hstay :=
      cmp99SourceParallelTransportPath_staysIn_of_coarseEndpoints
        (Nc := Nc) Omega y mu hy hy' x.1 x.2
    have htransport :=
      cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_pathTransport
        Omega rho U hspacing phi hD
        (cmp99SourceParallelTransportPath (G := SUN Nc) x.1 mu)
        hstay hxOmega hxTarget
    have hzero :
        extendZeroZeroCLM Omega phi x.1 -
            rho.adCLM
              ((cmp99SourceParallelTransportPath (G := SUN Nc)
                (M := M) (N' := N') x.1 mu).holonomy U)
              (extendZeroZeroCLM Omega phi
                (cmp99SourceTranslatedSite x.1 mu)) = 0 := by
      apply sub_eq_zero.mpr
      simpa only [
        extendZeroZeroCLM_apply_of_mem Omega phi x.1 hxOmega,
        extendZeroZeroCLM_apply_of_mem Omega phi
          (cmp99SourceTranslatedSite x.1 mu) hxTarget] using htransport
    rw [hzero, map_zero]

/-- The remaining coarse derivative on an internal bond is exactly the
`Ubar` transport remainder; no Dirichlet boundary energy enters. -/
theorem covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0)
    (y : FinBox d N') (mu : Fin d)
    (hy : y ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (hy' : y.shift mu ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites) :
    covariantD0CLM rho V
        (cmp99FullSourceBlockAverage rho U (extendZeroZeroCLM Omega phi))
        (y, mu) =
      cmp99SourceCoarseTransportRemainder rho U V
        (extendZeroZeroCLM Omega phi) y mu := by
  rw [covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder,
    cmp99SourceParallelAverageDefectValue_extendZero_eq_zero
      Omega rho U hspacing phi hD y mu hy hy', zero_add]

end

end YangMills.RG
