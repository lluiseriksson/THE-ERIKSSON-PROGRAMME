import YangMills.RG.BalabanCMP89SourceNeumannInternalBondTransport
import YangMills.RG.BalabanCMP99SourceRetainedCarrierEndpointGeometry

/-!
# Exact path transport from the CMP89 Neumann derivative

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

This leaf promotes the internal-bond equality to a literal Wilson-line
transport along any oriented path whose edges stay inside the regional site
carrier.  It does not assume global connectivity, identify a retained
average, or prove the Neumann joint-kernel theorem.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A zero normalized Neumann derivative transports the regional field
exactly along every path contained in the same active region. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_pathTransport
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0)
    {a b : FinBox d (M * N')}
    (Gamma : OrientedLatticePath (G := SUN Nc) a b)
    (hstay : Gamma.StaysIn Omega.sites)
    (ha : a ∈ Omega.sites) (hb : b ∈ Omega.sites) :
    phi ⟨a, ha⟩ =
      rho.adCLM (Gamma.holonomy U) (phi ⟨b, hb⟩) := by
  let psi : PhysicalGaugeZeroCochain d (M * N') Nc :=
    extendZeroZeroCLM Omega phi
  have hedge : ∀ e ∈ Gamma.edges,
      ‖covariantEdgeDefect rho U psi e‖ = 0 := by
    intro e he
    have hends :
        CMP99PhysicalBondEndpointsIn Omega.sites (physicalBondOfEdge e) :=
      physicalBondOfEdge_endpointsIn_of_staysIn hstay he
    have hbond : physicalBondOfEdge e ∈ Omega.bonds := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends⟩
    let be : ActiveGaugeRegion.Bond Omega :=
      ⟨physicalBondOfEdge e, hbond⟩
    have htransport :=
      cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_internalBond
        Omega rho U hspacing phi hD be
    have hcov :
        covariantD0CLM rho U psi (physicalBondOfEdge e) = 0 := by
      have hsub := sub_eq_zero.mpr htransport
      change
        psi (physicalBondOfEdge e).1 -
            rho.adCLM
              (U (ConcreteEdge.mk (physicalBondOfEdge e).1
                (physicalBondOfEdge e).2 true))
              (psi ((physicalBondOfEdge e).1.shift
                (physicalBondOfEdge e).2)) = 0
      simpa [psi,
        extendZeroZeroCLM_apply_of_mem Omega phi _ hends.1,
        extendZeroZeroCLM_apply_of_mem Omega phi _ hends.2,
        be] using hsub
    rw [norm_covariantEdgeDefect_eq, hcov, norm_zero]
  have hpath := norm_covariantPathDefect_le_sum rho U psi
    Gamma.edges a Gamma.isPath
  rw [Gamma.ends] at hpath
  have hsum :
      (Gamma.edges.map (fun e => ‖covariantEdgeDefect rho U psi e‖)).sum = 0 := by
    have aux : ∀ es : List (ConcreteEdge d (M * N')),
        (∀ e ∈ es, ‖covariantEdgeDefect rho U psi e‖ = 0) →
          (es.map (fun e => ‖covariantEdgeDefect rho U psi e‖)).sum = 0 := by
      intro es hes
      induction es with
      | nil => rfl
      | cons e es ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [hes e (by simp), ih (fun f hf => hes f (by simp [hf])), zero_add]
    exact aux Gamma.edges hedge
  rw [hsum] at hpath
  have hnorm :
      ‖psi a - rho.adCLM (Gamma.holonomy U) (psi b)‖ = 0 :=
    le_antisymm hpath (norm_nonneg _)
  have hzero := norm_eq_zero.mp hnorm
  have hpsiA : psi a = phi ⟨a, ha⟩ := by
    exact extendZeroZeroCLM_apply_of_mem Omega phi a ha
  have hpsiB : psi b = phi ⟨b, hb⟩ := by
    exact extendZeroZeroCLM_apply_of_mem Omega phi b hb
  rw [hpsiA, hpsiB] at hzero
  exact sub_eq_zero.mp hzero

end

end YangMills.RG
