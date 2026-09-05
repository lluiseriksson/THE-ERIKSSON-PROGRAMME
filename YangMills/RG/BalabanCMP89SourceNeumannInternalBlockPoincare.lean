import YangMills.RG.BalabanCMP89SourceNeumannInternalBlockEnergy
import YangMills.RG.BalabanCMP99FiniteMeanControl
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!
# One-block Poincare estimate for the CMP89 Neumann derivative

This leaf combines the literal block-contained contours with the same-block
Neumann energy.  It proves the quantitative estimate on one active complete
block only.  Summation over the active region and the explicit lattice-
spacing conversion are separate later bricks.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A literal source contour inside an active complete block is controlled
by that block's same-block Neumann energy. -/
theorem norm_cmp99BlockContainedContour_defect_sq_le_neumannInternalBlockEnergy
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega))
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) :
    let base : ActiveGaugeRegion.Site Omega :=
      ⟨blockBasepoint M N' y.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega y.1).mp y.2
            ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
              (blockSite_blockBasepoint M N' y.1))⟩
    ‖phi base -
        rho.adCLM
          (cmp99ContourHolonomy
            (cmp99BlockContainedContourSystem (G := SUN Nc)) U y.1 x.1)
          (phi (cmp99ActiveFineSiteOfBlock Omega y x))‖ ^ 2 ≤
      ((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
  let Gamma := cmp99BlockContainedContourSystem (G := SUN Nc) y.1 x.1
  let base : ActiveGaugeRegion.Site Omega :=
    ⟨blockBasepoint M N' y.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
          ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
            (blockSite_blockBasepoint M N' y.1))⟩
  let xa : ActiveGaugeRegion.Site Omega :=
    cmp99ActiveFineSiteOfBlock Omega y x
  let psi : PhysicalGaugeZeroCochain d (M * N') Nc :=
    extendZeroZeroCLM Omega phi
  have hsq := norm_covariantPathDefect_sq_le_length_mul_energy
    rho U psi Gamma
  have henergy :=
    covariantPathEnergy_le_length_mul_neumannInternalBlockEnergy
      Omega rho U phi y
        (cmp99BlockContainedContourSystem_staysIn
          (G := SUN Nc) y.1 x.1 x.2)
  have hlen : (Gamma.edges.length : ℝ) ≤
      ((d * (M - 1) : ℕ) : ℝ) := by
    exact_mod_cast
      cmp99BlockContainedContourSystem_length_le (G := SUN Nc) y.1 x.1 x.2
  have hblock :=
    cmp89SourceNeumannInternalBlockEnergy_nonneg Omega rho U phi y
  have hpsiBase : psi base.1 = phi base :=
    extendZeroZeroCLM_apply_of_mem Omega phi base.1 base.2
  have hpsiX : psi xa.1 = phi xa :=
    extendZeroZeroCLM_apply_of_mem Omega phi xa.1 xa.2
  change ‖phi base - rho.adCLM (Gamma.holonomy U) (phi xa)‖ ^ 2 ≤ _
  calc
    ‖phi base - rho.adCLM (Gamma.holonomy U) (phi xa)‖ ^ 2 ≤
      (Gamma.edges.length : ℝ) *
          covariantPathEnergy rho U psi Gamma.edges := by
            change ‖psi base.1 -
              rho.adCLM (Gamma.holonomy U) (psi xa.1)‖ ^ 2 ≤ _ at hsq
            rw [hpsiBase, hpsiX] at hsq
            exact hsq
    _ ≤ (Gamma.edges.length : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
      calc
        (Gamma.edges.length : ℝ) *
            covariantPathEnergy rho U psi Gamma.edges ≤
          (Gamma.edges.length : ℝ) *
            ((Gamma.edges.length : ℝ) *
              cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) := by
                exact mul_le_mul_of_nonneg_left henergy (by positivity)
        _ = _ := by ring
    _ ≤ ((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y := by
      have hsqLen : (Gamma.edges.length : ℝ) ^ 2 ≤
          ((d * (M - 1) : ℕ) : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hsqLen hblock

/-- Summing the contour defects over one complete active block costs exactly
its cardinality `M^d`, never the ambient volume. -/
theorem sum_norm_cmp99BlockContainedContour_defect_sq_le_neumann
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    let base : ActiveGaugeRegion.Site Omega :=
      ⟨blockBasepoint M N' y.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega y.1).mp y.2
            ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
              (blockSite_blockBasepoint M N' y.1))⟩
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        ‖phi base -
          rho.adCLM
            (cmp99ContourHolonomy
              (cmp99BlockContainedContourSystem (G := SUN Nc)) U y.1 x.1)
            (phi (cmp99ActiveFineSiteOfBlock Omega y x))‖ ^ 2 ≤
      (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) := by
  let base : ActiveGaugeRegion.Site Omega :=
    ⟨blockBasepoint M N' y.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
          ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
            (blockSite_blockBasepoint M N' y.1))⟩
  calc
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        ‖phi base -
          rho.adCLM
            (cmp99ContourHolonomy
              (cmp99BlockContainedContourSystem (G := SUN Nc)) U y.1 x.1)
            (phi (cmp99ActiveFineSiteOfBlock Omega y x))‖ ^ 2 ≤
      ∑ _x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
          cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) := by
            apply Finset.sum_le_sum
            intro x _hx
            exact
              norm_cmp99BlockContainedContour_defect_sq_le_neumannInternalBlockEnergy
                Omega rho U phi y x
    _ = (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        blockOf_card, nsmul_eq_mul]
      norm_cast

/-- Quantitative one-block estimate with the literal source-normalized
transported average and the same-block Neumann energy. -/
theorem sum_norm_sq_active_block_le_neumannEnergy_add_average
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    (∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
      ‖phi (cmp99ActiveFineSiteOfBlock Omega y x)‖ ^ 2) ≤
      6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) +
      3 * (M : ℝ) ^ d *
        ‖cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho U) phi y‖ ^ 2 := by
  let I := {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}
  let baseSite : ActiveGaugeRegion.Site Omega :=
    ⟨blockBasepoint M N' y.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y.1).mp y.2
          ((mem_blockOf M N' y.1 (blockBasepoint M N' y.1)).2
            (blockSite_blockBasepoint M N' y.1))⟩
  let base : SUNLieCoord Nc := phi baseSite
  let v : I → SUNLieCoord Nc := fun x =>
    cmp99SourceWeightedPhysicalTransport rho U y.1 x.1
      (phi (cmp99ActiveFineSiteOfBlock Omega y x))
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  have hnorm : cmp99SourceBlockAverageWeight M d *
      (Fintype.card I : ℝ) = 1 := by
    change cmp99SourceBlockAverageWeight M d *
      (Fintype.card {x : FinBox d (M * N') // x ∈ blockOf M N' y.1} : ℝ) = 1
    rw [Fintype.card_coe, blockOf_card, Nat.cast_pow]
    exact cmp99SourceBlockAverageWeight_mul_card (M := M) (d := d)
  have hmean :=
    sum_norm_sq_le_six_sum_base_defect_sq_add_three_card_mean_sq
      (I := I) (E := SUNLieCoord Nc)
      (cmp99SourceBlockAverageWeight M d) hw hnorm base v
  have hleft :
      (∑ x : I, ‖phi (cmp99ActiveFineSiteOfBlock Omega y x)‖ ^ 2) =
        ∑ x : I, ‖v x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [v, cmp99SourceWeightedPhysicalTransport,
      cmp99AdjointBlockTransport_apply]
    rw [rho.norm_ad]
  have hdefect : (∑ x : I, ‖base - v x‖ ^ 2) ≤
      (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) := by
    simpa only [I, base, baseSite, v,
      cmp99SourceWeightedPhysicalTransport,
      cmp99AdjointBlockTransport_apply] using
        sum_norm_cmp99BlockContainedContour_defect_sq_le_neumann
          Omega rho U phi y
  have hcard : (Fintype.card I : ℝ) = (M : ℝ) ^ d := by
    change (Fintype.card
      {x : FinBox d (M * N') // x ∈ blockOf M N' y.1} : ℝ) = _
    rw [Fintype.card_coe, blockOf_card]
    norm_cast
  have hmeanValue :
      cmp99SourceBlockAverageWeight M d • (∑ x : I, v x) =
        cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho U) phi y := by
    rw [cmp99SourceTransportedBlockAverageCLM,
      cmp99TransportedBlockAverageCLM_apply]
  rw [hleft]
  calc
    ∑ x : I, ‖v x‖ ^ 2 ≤
        6 * (∑ x : I, ‖base - v x‖ ^ 2) +
          3 * (Fintype.card I : ℝ) *
            ‖cmp99SourceBlockAverageWeight M d • (∑ x : I, v x)‖ ^ 2 :=
      hmean
    _ ≤ 6 * ((M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
          cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y)) +
        3 * (M : ℝ) ^ d *
          ‖cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho U) phi y‖ ^ 2 := by
      rw [hcard, hmeanValue]
      gcongr
    _ = _ := by ring

end

end YangMills.RG
