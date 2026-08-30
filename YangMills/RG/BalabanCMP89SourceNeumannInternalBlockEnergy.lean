import YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision
import YangMills.RG.BalabanCMP99SourceRetainedCarrierEndpointGeometry
import YangMills.RG.BalabanCMP99SourceRegionalCoarseAverage

/-!
# Internal-block energy for the CMP89 Neumann derivative

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The existing CMP99 block energy assigns every positive bond by its source
site.  That convention is correct for the ambient/Dirichlet derivative but
also charges bonds leaving an active block.  CMP89 uses a Neumann rectangle:
only bonds whose two endpoints are retained may enter its energy.

This leaf therefore defines the literal same-block part of the unnormalised
regional Neumann derivative and proves the edge and path estimates needed by
the quantitative one-scale Poincare argument.  The lattice-spacing factor is
not absorbed here; the later norm comparison will expose it explicitly.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The unnormalised internal-bond derivative on a CMP89 Neumann region. -/
noncomputable def cmp89SourceNeumannRegionalRawD0
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ActiveGaugeOneCochain Omega (SUNLieCoord Nc) :=
  restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega
    (covariantD0CLM rho U (extendZeroZeroCLM Omega phi))

/-- Energy of retained positive bonds whose two endpoints belong to the same
active order-`M` block.  The two-endpoint predicate is orientation-safe. -/
noncomputable def cmp89SourceNeumannInternalBlockEnergy
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) : ℝ := by
  classical
  exact
    ∑ b : ActiveGaugeRegion.Bond Omega,
      if CMP99PhysicalBondEndpointsIn (blockOf M N' y.1) b.1 then
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2
      else 0

theorem cmp89SourceNeumannInternalBlockEnergy_nonneg
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    0 ≤ cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
  unfold cmp89SourceNeumannInternalBlockEnergy
  exact Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

/-- Every squared edge defect on a block-contained path is bounded by the
literal same-block Neumann energy. -/
theorem norm_covariantEdgeDefect_sq_le_neumannInternalBlockEnergy
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := SUN Nc) a b}
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
    (hstay : Gamma.StaysIn (blockOf M N' y.1))
    {e : ConcreteEdge d (M * N')} (he : e ∈ Gamma.edges) :
    ‖covariantEdgeDefect rho U (extendZeroZeroCLM Omega phi) e‖ ^ 2 ≤
      cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
  classical
  have hendsBlock :
      CMP99PhysicalBondEndpointsIn (blockOf M N' y.1)
        (physicalBondOfEdge e) :=
    physicalBondOfEdge_endpointsIn_of_staysIn hstay he
  have hblock : blockOf M N' y.1 ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (M := M) (N' := N') Omega y.1).mp y.2
  have hendsOmega :
      CMP99PhysicalBondEndpointsIn Omega.sites (physicalBondOfEdge e) :=
    hendsBlock.mono hblock
  have hbond : physicalBondOfEdge e ∈ Omega.bonds :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hendsOmega⟩
  let be : ActiveGaugeRegion.Bond Omega :=
    ⟨physicalBondOfEdge e, hbond⟩
  rw [norm_covariantEdgeDefect_eq]
  unfold cmp89SourceNeumannInternalBlockEnergy
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (ActiveGaugeRegion.Bond Omega)))
    (f := fun b =>
      if CMP99PhysicalBondEndpointsIn (blockOf M N' y.1) b.1 then
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2
      else 0)
    (fun b _ => by dsimp; split_ifs <;> positivity)
    (Finset.mem_univ be)
  simpa [be, hendsBlock, cmp89SourceNeumannRegionalRawD0] using h

/-- A block-contained path costs its length times the same-block Neumann
energy.  Repeated edges need no simplicity assumption. -/
theorem covariantPathEnergy_le_length_mul_neumannInternalBlockEnergy
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := SUN Nc) a b}
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
    (hstay : Gamma.StaysIn (blockOf M N' y.1)) :
    covariantPathEnergy rho U (extendZeroZeroCLM Omega phi) Gamma.edges ≤
      (Gamma.edges.length : ℝ) *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
  rw [covariantPathEnergy]
  calc
    (Gamma.edges.map (fun e =>
        ‖covariantEdgeDefect rho U (extendZeroZeroCLM Omega phi) e‖ ^ 2)).sum ≤
      (Gamma.edges.map (fun _e =>
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y)).sum := by
          apply List.sum_le_sum
          intro e he
          exact norm_covariantEdgeDefect_sq_le_neumannInternalBlockEnergy
            Omega rho U phi y hstay he
    _ = (Gamma.edges.length : ℝ) *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by simp

end

end YangMills.RG
