import YangMills.RG.BalabanCMP99SourceUbarExactReadCarrier
import YangMills.RG.BalabanCMP99SourceRegionalScale

/-!


# Local fine-link bound for the literal Ubar deviation

The existing source estimate assumes fine-link smallness on the complete
torus.  Its proof actually reads only the straight base path and the three
literal Ubar contours of the selected coarse bond.  This module repeats that
estimate with smallness restricted to the exact f2b read carrier.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A bound on the positive physical coordinate controls either orientation
of the same gauge edge. -/
theorem norm_gaugeConfig_apply_sub_one_le_of_positivePhysicalBond
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (epsilon : ℝ)
    (h : ‖(U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e)) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon := by
  cases e with
  | mk x mu sign =>
      cases sign
      · have hU := U.map_reverse (ConcreteEdge.mk x mu true)
        change U (ConcreteEdge.mk x mu false) =
          (U (ConcreteEdge.mk x mu true))⁻¹ at hU
        rw [hU]
        exact (norm_sun_inv_sub_one_le _).trans h
      · exact h

/-- The straight coarse base path is controlled by smallness only on the
selected Ubar read carrier. -/
theorem norm_cmp99SourceBaseCoarseBackground_sub_one_le_of_readBonds
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (b : PhysicalBond d N')
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    ‖(cmp99SourceBaseCoarseBackground background
        (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (M : ℝ) * epsilonFine := by
  rw [cmp99SourceBaseCoarseBackground_apply_pos]
  change
    ‖((wilsonLine background
        (cmp99SourceParallelTransportPath (G := SUN Nc)
          (blockBasepoint M N' b.1) b.2).edges : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (M : ℝ) * epsilonFine
  simpa only [cmp99SourceParallelTransportPath_length] using
    norm_wilsonLine_sub_one_le_length_mul background
      (cmp99SourceParallelTransportPath (G := SUN Nc)
        (blockBasepoint M N' b.1) b.2).edges epsilonFine (by
          intro e he
          apply norm_gaugeConfig_apply_sub_one_le_of_positivePhysicalBond
          exact fineSmall _
            (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_base
              b e he))

/-- Local version of the literal CMP109 deviation estimate.  No link outside
the exact carrier of the selected coarse bond is used. -/
theorem norm_cmp99SourceUbarDeviationLogArg_le_fineRadius_of_readBonds
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (b : PhysicalBond d N')
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    ‖UbarDeviationLogArg
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        background (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b) x
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤
      cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
  let Gamma1 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma1 (G := SUN Nc) b
  let Gamma2 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma2 (G := SUN Nc) b
  let Gamma3 : FinBox d (M * N') → List (ConcreteEdge d (M * N')) :=
    cmp99SourceUbarGamma3 (G := SUN Nc) b
  have h1 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma1 x) epsilonFine (by
      intro e he
      apply norm_gaugeConfig_apply_sub_one_le_of_positivePhysicalBond
      exact fineSmall _
        (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma1
          b x hx e he))
  have h2 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma2 x) epsilonFine (by
      intro e he
      apply norm_gaugeConfig_apply_sub_one_le_of_positivePhysicalBond
      exact fineSmall _
        (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma2
          b x hx e he))
  have h3 := norm_wilsonLine_sub_one_le_length_mul background
    (Gamma3 x) epsilonFine (by
      intro e he
      apply norm_gaugeConfig_apply_sub_one_le_of_positivePhysicalBond
      exact fineSmall _
        (physicalBondOfEdge_mem_cmp99SourceUbarFineReadBonds_of_gamma3
          b x hx e he))
  have hc := norm_cmp99SourceBaseCoarseBackground_sub_one_le_of_readBonds
    background epsilonFine b fineSmall
  have hGamma1 : (Gamma1 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma1_length_le (G := SUN Nc) b x hx
  have hGamma2 : (Gamma2 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma2_length_le (G := SUN Nc) hd hM b x
  have hGamma3 : (Gamma3 x).length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma3_length_le (G := SUN Nc) b x hx
  calc
    _ ≤ ‖((wilsonLine background (Gamma1 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine background (Gamma2 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine background (Gamma3 x) : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖(cmp99SourceBaseCoarseBackground background
            (positiveEdgeOfPhysicalBond b) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ :=
      norm_UbarDeviationLogArg_le_four_factors
        background (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b) x Gamma1 Gamma2 Gamma3
    _ ≤ ((Gamma1 x).length : ℝ) * epsilonFine +
        ((Gamma2 x).length : ℝ) * epsilonFine +
        ((Gamma3 x).length : ℝ) * epsilonFine +
        (M : ℝ) * epsilonFine := by gcongr
    _ ≤ ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        ((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
        (M : ℝ) * epsilonFine := by
      gcongr
    _ = cmp99SourceUbarFineDeviationRadius d M epsilonFine := by
      simp only [cmp99SourceUbarFineDeviationRadius, Nat.cast_add,
        Nat.cast_mul]
      ring

end

end YangMills.RG
