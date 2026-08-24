import YangMills.RG.BalabanCMP99SourceRetainedExactReadCarrier
import YangMills.RG.BalabanCMP99SourceRegionalScale

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Selected-bond locality of the literal source next background

The direct-deviation-budget constructor stores proof terms certifying that its
special-unitary value is legal.  Those proofs do not affect the represented
matrix.  This module exposes that fact, lifts exact raw-Ubar locality through
the `SUN` constructor, and specializes it to the canonical source regional
scale on a selected family of coarse bonds.

No equality of complete next backgrounds is asserted.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The direct-budget physical Ubar block represents the same literal matrix
`Ubar`; its budget and deviation proof certify membership in `SUN` only. -/
theorem cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar
    (A_fine : GaugeConfig d (M * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Γ_1 Γ_2 Γ_3 : PhysicalBond d N' → FinBox d (M * N') → List FineEdge)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Γ_1 b) (Γ_2 b) (Γ_3 b)‖ ≤ B.δ)
    (b : PhysicalBond d N') :
    (cmp99PhysicalUbarBlockOfDeviationBudget
        A_fine A_coarse Γ_1 Γ_2 Γ_3 B hdev b :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        A_fine A_coarse (positiveEdgeOfPhysicalBond b)
        (Γ_1 b) (Γ_2 b) (Γ_3 b) := by
  change NormedSpace.exp
      (∑ x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)),
        (M ^ d : ℝ)⁻¹ • nearLog
          (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
            (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
    NormedSpace.exp
      ((M ^ d : ℝ)⁻¹ •
        ∑ x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)),
          nearLog
            (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
              (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
                Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ)
  apply congrArg (fun Z : Matrix (Fin Nc) (Fin Nc) ℂ =>
    NormedSpace.exp Z *
      (A_coarse (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ))
  exact (Finset.smul_sum
    (r := (M ^ d : ℝ)⁻¹)
    (s := blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)))
    (f := fun x => nearLog
      (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
        (Γ_1 b) (Γ_2 b) (Γ_3 b) : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1))).symm

/-- Raw-Ubar locality lifts to equality of the direct-budget `SUN` values on
every selected coarse bond.  The budgets and proof witnesses may differ. -/
theorem cmp99PhysicalUbarBlockOfDeviationBudget_eq_of_eqOn_selectedReadBonds
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (coarseBonds : Finset (PhysicalBond d N'))
    (B_U B_V : MatrixNearLogNoWindingBudget Nc)
    (hdevU : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B_U.δ)
    (hdevV : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          V (cmp99SourceBaseCoarseBackground V)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B_V.δ)
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    cmp99PhysicalUbarBlockOfDeviationBudget U
        (cmp99SourceBaseCoarseBackground U)
        (cmp99SourceUbarGamma1 (G := SUN Nc))
        (cmp99SourceUbarGamma2 (G := SUN Nc))
        (cmp99SourceUbarGamma3 (G := SUN Nc)) B_U hdevU b =
      cmp99PhysicalUbarBlockOfDeviationBudget V
        (cmp99SourceBaseCoarseBackground V)
        (cmp99SourceUbarGamma1 (G := SUN Nc))
        (cmp99SourceUbarGamma2 (G := SUN Nc))
        (cmp99SourceUbarGamma3 (G := SUN Nc)) B_V hdevV b := by
  apply Subtype.ext
  rw [cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar,
    cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar]
  exact cmp99SourcePhysicalUbar_eq_of_eqOn_selectedReadBonds
    U V coarseBonds hUV b hb

/-- Selected positive coordinates of the literal source next backgrounds are
equal whenever the two fine configurations agree on their generated Ubar read
carrier.  The complete coarse configurations need not be equal. -/
theorem cmp99SourceRegionalScaleDataOfDeviationBudget_nextBackground_apply_pos_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (weightU weightV : ℝ)
    (B_U B_V : MatrixNearLogNoWindingBudget Nc)
    (hdevU : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B_U.δ)
    (hdevV : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          V (cmp99SourceBaseCoarseBackground V)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B_V.δ)
    (coarseBonds : Finset (PhysicalBond d N'))
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    (cmp99SourceRegionalScaleDataOfDeviationBudget hd hM Omega U weightU
        B_U hdevU).nextBackground (positiveEdgeOfPhysicalBond b) =
      (cmp99SourceRegionalScaleDataOfDeviationBudget hd hM Omega V weightV
        B_V hdevV).nextBackground (positiveEdgeOfPhysicalBond b) := by
  simp only [CMP99PhysicalRegionalScaleData.nextBackground,
    cmp99SourceRegionalScaleDataOfDeviationBudget,
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_pos]
  exact cmp99PhysicalUbarBlockOfDeviationBudget_eq_of_eqOn_selectedReadBonds
    U V coarseBonds B_U B_V hdevU hdevV hUV b hb

/-- Source-normalized specialization used by the retained-tower induction.
Both scales are built internally by `ofFineSmall`; only fine-background
agreement on the generated selected carrier is assumed. -/
theorem cmp99SourceNormalizedRegionalScaleOfFineSmall_nextBackground_apply_pos_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (U V : PhysicalGaugeBackground d (M * N') Nc)
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (fineSmallU : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (fineSmallV : ∀ e : ConcreteEdge d (M * N'),
      ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (coarseBonds : Finset (PhysicalBond d N'))
    (hUV : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      U (positiveEdgeOfPhysicalBond q) =
        V (positiveEdgeOfPhysicalBond q))
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    let ScaleU := CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
      Omega U hOmega epsilon epsilon_nonneg noWinding fineSmallU
    let ScaleV := CMP99SourceNormalizedRegionalScale.ofFineSmall hd hM
      Omega V hOmega epsilon epsilon_nonneg noWinding fineSmallV
    ScaleU.toSourceScale.data.nextBackground (positiveEdgeOfPhysicalBond b) =
      ScaleV.toSourceScale.data.nextBackground
        (positiveEdgeOfPhysicalBond b) := by
  dsimp only
  apply cmp99SourceRegionalScaleDataOfDeviationBudget_nextBackground_apply_pos_eq
    hd hM Omega U V (cmp99SourceBlockAverageWeight M d)
      (cmp99SourceBlockAverageWeight M d)
      (cmp99SourceUbarFineNoWindingBudget epsilon noWinding)
      (cmp99SourceUbarFineNoWindingBudget epsilon noWinding)
  · intro b' x hx
    simpa only [cmp99SourceUbarFineNoWindingBudget_delta] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
        hd hM U epsilon epsilon_nonneg fineSmallU b' x hx
  · intro b' x hx
    simpa only [cmp99SourceUbarFineNoWindingBudget_delta] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
        hd hM V epsilon epsilon_nonneg fineSmallV b' x hx
  · exact coarseBonds
  · exact hUV
  · exact b
  · exact hb

end

end YangMills.RG
