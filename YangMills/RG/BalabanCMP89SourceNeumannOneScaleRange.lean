import YangMills.RG.BalabanCMP89SourceNeumannPathTransport
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!
# Exact one-scale range identity for the CMP89 Neumann kernel

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

A field in the kernel of the normalized regional Neumann derivative is
parallel along every block-contained source contour.  Consequently the
literal `M^{-d}` transported average is its value at the block basepoint,
and the printed unit-coefficient synthesis reconstructs the original field.

This is a one-scale statement.  It does not yet identify the recursively
generated retained tower or prove the terminal joint-kernel theorem.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- On the Neumann kernel, the literal source-normalized average is exactly
the field at the selected block basepoint.  The proof exposes the cancellation
`M^{-d} * M^d = 1`; no counting cardinality is hidden in a constant. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_blockAverage
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0)
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) phi y =
      phi ⟨blockBasepoint M N' y.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega y.1).mp y.2
            ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
              (blockSite_blockBasepoint M N' y.1))⟩ := by
  let base : ActiveGaugeRegion.Site Omega :=
    ⟨blockBasepoint M N' y.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
          ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
            (blockSite_blockBasepoint M N' y.1))⟩
  have hterm : ∀ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
      cmp99SourceWeightedPhysicalTransport rho U y.1 x.1
          (phi (cmp99ActiveFineSiteOfBlock Omega y x)) =
        phi base := by
    intro x
    have hstayBlock := cmp99BlockContainedContourSystem_staysIn
      (G := SUN Nc) y.1 x.1 x.2
    have hblock : blockOf M N' y.1 ⊆ Omega.sites :=
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
    have hstay :
        (cmp99BlockContainedContourSystem (G := SUN Nc) y.1 x.1).StaysIn
          Omega.sites := by
      intro e he
      exact ⟨hblock (hstayBlock e he).1, hblock (hstayBlock e he).2⟩
    have hxOmega : x.1 ∈ Omega.sites :=
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2 x.2
    have hpath :=
      cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_pathTransport
        Omega rho U hspacing phi hD
        (cmp99BlockContainedContourSystem (G := SUN Nc) y.1 x.1)
        hstay base.2 hxOmega
    simpa [base, cmp99SourceWeightedPhysicalTransport,
      cmp99AdjointBlockTransport, cmp99ContourHolonomy] using hpath.symm
  rw [cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, blockOf_card,
    ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_pow]
  change cmp99SourceBlockAverageWeight M d • ((M : ℝ) ^ d • phi base) =
    phi base
  rw [← mul_smul, cmp99SourceBlockAverageWeight_mul_card, one_smul]

/-- The printed unit synthesis is a left inverse of the physical one-scale
average on the exact Neumann kernel.  This is the source-facing range identity
needed before recursive tower transport can be attempted. -/
theorem cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0) :
    cmp99SourceTransportedBlockWeightedAdjointCLM Omega hOmega
        (cmp99SourceWeightedPhysicalTransport rho U)
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho U) phi) =
      phi := by
  apply PiLp.ext
  intro x
  rw [cmp99SourceTransportedBlockWeightedAdjointCLM,
    cmp99TransportedBlockSynthesisCLM_apply, one_smul]
  let y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
    ⟨blockSite M N' x.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega (blockSite M N' x.1)).2
          (hOmega x.1 x.2)⟩
  rw [cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_blockAverage
    Omega rho U hspacing phi hD y]
  have hxBlock : x.1 ∈ blockOf M N' y.1 :=
    (mem_blockOf M N' y.1 x.1).2 rfl
  have hstayBlock := cmp99BlockContainedContourSystem_staysIn
    (G := SUN Nc) y.1 x.1 hxBlock
  have hblock : blockOf M N' y.1 ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (M := M) (N' := N') Omega y.1).mp y.2
  have hstay :
      (cmp99BlockContainedContourSystem (G := SUN Nc) y.1 x.1).StaysIn
        Omega.sites := by
    intro e he
    exact ⟨hblock (hstayBlock e he).1, hblock (hstayBlock e he).2⟩
  let base : ActiveGaugeRegion.Site Omega :=
    ⟨blockBasepoint M N' y.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
          ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
            (blockSite_blockBasepoint M N' y.1))⟩
  have hpath :=
    cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_pathTransport
      Omega rho U hspacing phi hD
      (cmp99BlockContainedContourSystem (G := SUN Nc) y.1 x.1)
      hstay base.2 x.2
  change
    (cmp99SourceWeightedPhysicalTransport rho U y.1 x.1).symm
        (phi base) = phi x
  have htransport :
      phi base =
        cmp99SourceWeightedPhysicalTransport rho U y.1 x.1 (phi x) := by
    simpa [base, cmp99SourceWeightedPhysicalTransport,
      cmp99AdjointBlockTransport, cmp99ContourHolonomy] using hpath
  rw [htransport]
  exact LinearIsometryEquiv.symm_apply_apply _ _

end

end YangMills.RG
