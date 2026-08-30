import YangMills.RG.BalabanCMP89SourceNeumannInternalBlockPoincare
import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision
import YangMills.RG.BalabanCMP99SourceActiveFineBlockEquiv
import YangMills.RG.BalabanCMP99OneScaleBlockPoincare

/-!
# Quantitative one-scale CMP89 Neumann Poincare producer

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The active fine region is reindexed by its complete owner blocks.  Every
same-block positive bond is charged at most once, while cross-block bonds are
discarded rather than turned into a Dirichlet boundary term.  This gives a
volume-free explicit Poincare constant for the literal one-scale transported
average.  The final conversion exposes `spacing^2` exactly.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Same-block energies over active owner blocks are dominated by the full
unnormalised Neumann internal-bond energy.  Cross-block bonds contribute zero
to the left and remain available on the right. -/
theorem sum_cmp89SourceNeumannInternalBlockEnergy_le_raw_norm_sq
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    (∑ y : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
      cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) ≤
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  unfold cmp89SourceNeumannInternalBlockEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _hb
  have hbends : CMP99PhysicalBondEndpointsIn Omega.sites b.1 := by
    exact (Finset.mem_filter.mp b.2).2
  let owner : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
    ⟨blockSite M N' b.1.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega (blockSite M N' b.1.1)).2
          (hOmega b.1.1 hbends.1)⟩
  have hother : ∀ y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
      y ≠ owner →
        (if CMP99PhysicalBondEndpointsIn (blockOf M N' y.1) b.1 then
          ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2
        else 0) = 0 := by
    intro y hy
    have hnot : ¬ CMP99PhysicalBondEndpointsIn (blockOf M N' y.1) b.1 := by
      intro hends
      apply hy
      apply Subtype.ext
      change y.1 = blockSite M N' b.1.1
      exact ((mem_blockOf M N' y.1 b.1.1).mp hends.1).symm
    simp [hnot]
  calc
    (∑ y : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
      if CMP99PhysicalBondEndpointsIn (blockOf M N' y.1) b.1 then
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2
      else 0) =
      (if CMP99PhysicalBondEndpointsIn (blockOf M N' owner.1) b.1 then
        ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2
      else 0) := by
        apply Fintype.sum_eq_single owner
        intro y hy
        exact hother y hy
    _ ≤ ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi b‖ ^ 2 := by
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _

/-- Exact normalization dictionary between the raw internal-bond derivative
and the CMP89 derivative carrying `spacing⁻¹`. -/
theorem norm_cmp89SourceNeumannRegionalRawD0_sq_eq_spacing_sq_mul
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 =
      spacing ^ 2 *
        ‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 := by
  have hraw : cmp89SourceNeumannRegionalRawD0 Omega rho U phi =
      spacing • cmp89SourceNeumannRegionalCovariantD0CLM
        Omega rho U spacing phi := by
    apply PiLp.ext
    intro b
    change
      restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega
          (covariantD0CLM rho U (extendZeroZeroCLM Omega phi)) b =
        spacing • (spacing⁻¹ •
          restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega
            (covariantD0CLM rho U (extendZeroZeroCLM Omega phi)) b)
    rw [← mul_smul, mul_inv_cancel₀ hspacing, one_smul]
  rw [hraw, norm_smul, Real.norm_eq_abs]
  nlinarith [sq_abs spacing]

/-- Explicit one-scale Neumann Poincare constant, with the lattice-spacing
convention carried in the same visible factor as in the Dirichlet analogue. -/
noncomputable def cmp89SourceNeumannOneScalePoincareConstant
    (d M : ℕ) (spacing : ℝ) : ℝ :=
  cmp99OneScaleBlockPoincareConstant d M * max (spacing ^ 2) 1

theorem cmp89SourceNeumannOneScalePoincareConstant_pos
    (spacing : ℝ) :
    0 < cmp89SourceNeumannOneScalePoincareConstant d M spacing := by
  unfold cmp89SourceNeumannOneScalePoincareConstant
  exact mul_pos cmp99OneScaleBlockPoincareConstant_pos
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))

/-- Quantitative volume-free one-scale Poincare estimate for the literal
CMP89 Neumann derivative and source-normalized transported average. -/
theorem norm_sq_le_cmp89SourceNeumannOneScalePoincare
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖phi‖ ^ 2 ≤
      cmp89SourceNeumannOneScalePoincareConstant d M spacing *
        (‖cmp89SourceNeumannRegionalCovariantD0CLM
            Omega rho U spacing phi‖ ^ 2 +
          ‖cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho U) phi‖ ^ 2) := by
  let A : ℝ :=
    6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2)
  let B : ℝ := 3 * (M : ℝ) ^ d
  let Q := cmp99SourceTransportedBlockAverageCLM Omega
    (cmp99SourceWeightedPhysicalTransport rho U)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsites := sum_activeGaugeRegion_eq_sum_activeBlocks Omega hOmega
    (fun x : ActiveGaugeRegion.Site Omega => ‖phi x‖ ^ 2)
  have hregional : ‖phi‖ ^ 2 ≤
      cmp99OneScaleBlockPoincareConstant d M *
        (‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 +
          ‖Q phi‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, hsites]
    calc
      (∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          ‖phi (cmp99ActiveFineSiteOfBlock Omega y x)‖ ^ 2) ≤
        ∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
          (A * cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y +
            B * ‖Q phi y‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro y _hy
              simpa only [A, B, Q, mul_assoc] using
                sum_norm_sq_active_block_le_neumannEnergy_add_average
                  Omega rho U phi y
      _ = A * (∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
            cmp89SourceNeumannInternalBlockEnergy Omega rho U phi y) +
          B * ‖Q phi‖ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              PiLp.norm_sq_eq_of_L2]
      _ ≤ A * ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 +
          B * ‖Q phi‖ ^ 2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (sum_cmp89SourceNeumannInternalBlockEnergy_le_raw_norm_sq
                  Omega hOmega rho U phi) hA)
              le_rfl
      _ ≤ max A B *
          (‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 +
            ‖Q phi‖ ^ 2) := by
        have hAle : A ≤ max A B := le_max_left _ _
        have hBle : B ≤ max A B := le_max_right _ _
        nlinarith [sq_nonneg ‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖,
          sq_nonneg ‖Q phi‖]
      _ = cmp99OneScaleBlockPoincareConstant d M *
          (‖cmp89SourceNeumannRegionalRawD0 Omega rho U phi‖ ^ 2 +
            ‖Q phi‖ ^ 2) := by rfl
  rw [norm_cmp89SourceNeumannRegionalRawD0_sq_eq_spacing_sq_mul
    Omega rho U hspacing phi] at hregional
  change ‖phi‖ ^ 2 ≤
    cmp99OneScaleBlockPoincareConstant d M * max (spacing ^ 2) 1 *
      (‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 + ‖Q phi‖ ^ 2)
  have hC : 0 ≤ cmp99OneScaleBlockPoincareConstant d M :=
    cmp99OneScaleBlockPoincareConstant_pos.le
  have hs : spacing ^ 2 ≤ max (spacing ^ 2) 1 := le_max_left _ _
  have hOne : 1 ≤ max (spacing ^ 2) 1 := le_max_right _ _
  have hD0 : 0 ≤ ‖cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi‖ ^ 2 := sq_nonneg _
  have hQ0 : 0 ≤ ‖Q phi‖ ^ 2 := sq_nonneg _
  calc
    ‖phi‖ ^ 2 ≤ cmp99OneScaleBlockPoincareConstant d M *
        (spacing ^ 2 * ‖cmp89SourceNeumannRegionalCovariantD0CLM
          Omega rho U spacing phi‖ ^ 2 + ‖Q phi‖ ^ 2) := hregional
    _ ≤ cmp99OneScaleBlockPoincareConstant d M * max (spacing ^ 2) 1 *
        (‖cmp89SourceNeumannRegionalCovariantD0CLM
            Omega rho U spacing phi‖ ^ 2 + ‖Q phi‖ ^ 2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        spacing ^ 2 * ‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho U spacing phi‖ ^ 2 + ‖Q phi‖ ^ 2 =
            spacing ^ 2 * ‖cmp89SourceNeumannRegionalCovariantD0CLM
              Omega rho U spacing phi‖ ^ 2 + 1 * ‖Q phi‖ ^ 2 := by ring
        _ ≤ max (spacing ^ 2) 1 *
              ‖cmp89SourceNeumannRegionalCovariantD0CLM
                Omega rho U spacing phi‖ ^ 2 +
            max (spacing ^ 2) 1 * ‖Q phi‖ ^ 2 :=
          add_le_add
            (mul_le_mul_of_nonneg_right hs hD0)
            (mul_le_mul_of_nonneg_right hOne hQ0)
        _ = _ := by ring

/-- The explicit producer inhabits the exact analytic gate consumed by the
CMP89 regional gauge precision. -/
theorem cmp89SourceNeumann_oneScale_quantitativePoincare
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0) :
    CMP89SourceNeumannRegionalPoincare Omega rho U
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U)) spacing
      (cmp89SourceNeumannOneScalePoincareConstant d M spacing) := by
  intro phi
  exact norm_sq_le_cmp89SourceNeumannOneScalePoincare
    Omega hOmega rho U hspacing phi

end

end YangMills.RG
