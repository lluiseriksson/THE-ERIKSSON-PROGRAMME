import YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion

/-!
# PRE-VALIDATION: full-side rectangle retains a torus wrap bond

Source present; .olean not materialized; not compiler-verified.
This finite geometric probe concerns the CURRENT bond predicate only.
It does not compare Green norms, refute a conditional reflection theorem,
or change the current precision. The integer endpoint leaves [0,3), while
the torus endpoint wraps to 0 and both torus endpoints remain active.
-/

namespace YangMills.RG

open YangMills

noncomputable section

private theorem wrapProbe_mem_bonds_of_endpoints
    {d N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (b : PositiveBond d N)
    (hb : b.1 ∈ Omega.sites ∧ b.1.shift b.2 ∈ Omega.sites) :
    b ∈ Omega.bonds := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩

private theorem wrapProbe_mem_bonds_of_full_sites
    {d N : ℕ} [NeZero N] (Omega : ActiveGaugeRegion d N)
    (hfull : Omega.sites = Finset.univ) (b : PositiveBond d N) :
    b ∈ Omega.bonds := by
  apply wrapProbe_mem_bonds_of_endpoints
  constructor
  · rw [hfull]
    exact Finset.mem_univ _
  · rw [hfull]
    exact Finset.mem_univ _

private def wrapProbeRegion : ActiveGaugeRegion 4 3 :=
  cmp89SourceNeumannRectangleActiveRegion (N := 3) (fun _ => 3)

private def wrapProbeSite : FinBox 4 3 := fun _ => 2

private theorem wrapProbeRegion_sites : wrapProbeRegion.sites = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  unfold wrapProbeRegion
  rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
  intro mu
  change (x mu).val < 3
  exact (x mu).isLt

/-- The existing non-strict site-fit hypothesis holds, but a retained torus
bond crosses the integer rectangle boundary. This is a bond-level witness,
not a claimed inequality between the associated inverses. -/
theorem neumannRectangle_siteFit_retains_wrapBond :
    (∀ mu : Fin 4, (3 : ℤ) ≤ (3 : ℕ)) ∧
      (wrapProbeSite, (0 : Fin 4)) ∈ wrapProbeRegion.bonds ∧
      ((wrapProbeSite.shift (0 : Fin 4)) (0 : Fin 4)).val = 0 ∧
      ¬ ((wrapProbeSite (0 : Fin 4)).val : ℤ) + 1 < 3 := by
  constructor
  · intro mu
    exact le_rfl
  constructor
  · with_reducible exact wrapProbe_mem_bonds_of_full_sites (d := 4) (N := 3)
      wrapProbeRegion wrapProbeRegion_sites (wrapProbeSite, (0 : Fin 4))
  constructor
  · rfl
  · norm_num [wrapProbeSite]

#print axioms neumannRectangle_siteFit_retains_wrapBond

end
end YangMills.RG
