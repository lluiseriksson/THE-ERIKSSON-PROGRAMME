import YangMills.RG.BalabanCMP99SourceGaugeDeviationTransport

/-!
PRE-VALIDATION: source is present only in scratch; no `.olean` has been
materialized and none of the declarations below is compiler-verified.

# Canonical regular/small CMP99 source scale pair

This is C6c.8c3--c4.  The only small-field certificate belongs to the gauge
transformed background.  The original-side deviation bound and both literal
Ubar backgrounds are constructed internally.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- One source-fixed scale on a regular background together with the
canonical scale on its small gauge representative.  The raw constructor is
private so callers cannot provide either data package or their covariance. -/
structure CMP99SourceGaugeRegularScalePair
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (u : GaugeTransform d (M * N') (SUN Nc)) where
  private mk ::
  blockSaturated : Omega.BlockSaturated
  originalData : CMP99PhysicalRegionalScaleData Omega background
  transformedData : CMP99PhysicalRegionalScaleData Omega (gaugeAct u background)
  original_weight_eq_source :
    originalData.weight = cmp99SourceBlockAverageWeight M d
  transformed_weight_eq_source :
    transformedData.weight = cmp99SourceBlockAverageWeight M d
  nextBackground_gaugeAct :
    transformedData.nextBackground =
      gaugeAct (coarseTransform u) originalData.nextBackground

/-- Build the regular/small pair from the one small representative supplied
by CMP99 (3.35).  No original-side linkwise smallness or deviation estimate
occurs in the interface. -/
noncomputable def cmp99SourceGaugeRegularScalePair
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (blockSaturated : Omega.BlockSaturated)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (transformedSmall : ∀ e : ConcreteEdge d (M * N'),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon) :
    CMP99SourceGaugeRegularScalePair Omega background u := by
  let B : MatrixNearLogNoWindingBudget Nc :=
    cmp99SourceUbarFineNoWindingBudget epsilon noWinding
  let transformedBackground := gaugeAct u background
  have hdevT : ∀ b : PhysicalBond d N',
      ∀ x : FinBox d (M * N'), x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          transformedBackground
          (cmp99SourceBaseCoarseBackground transformedBackground)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B.δ := by
    intro b x hx
    simpa only [B, cmp99SourceUbarFineNoWindingBudget_delta] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius
        hd hM transformedBackground epsilon epsilon_nonneg
        transformedSmall b x hx
  have hdev : ∀ b : PhysicalBond d N',
      ∀ x : FinBox d (M * N'), x ∈ blockOf M N' b.1 →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          background (cmp99SourceBaseCoarseBackground background)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ B.δ := by
    intro b x hx
    have hT := hdevT b x hx
    rw [cmp99SourceBaseCoarseBackground_gaugeAct u background] at hT
    have hnorm := norm_UbarDeviationLogArg_gaugeAct_eq
      u background (cmp99SourceBaseCoarseBackground background)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b)
      (cmp99SourceUbarGamma1_path (G := SUN Nc) b x hx)
      (cmp99SourceUbarGamma1_end (G := SUN Nc) b x hx)
      (cmp99SourceUbarGamma2_path (G := SUN Nc) b x)
      (cmp99SourceUbarGamma3_path (G := SUN Nc) b x hx)
      (cmp99SourceUbarGamma3_end (G := SUN Nc) b x hx)
    rw [hnorm] at hT
    exact hT
  let originalData := cmp99SourceRegionalScaleDataOfDeviationBudget
    hd hM Omega background (cmp99SourceBlockAverageWeight M d) B hdev
  let transformedData := cmp99SourceRegionalScaleDataOfDeviationBudget
    hd hM Omega transformedBackground (cmp99SourceBlockAverageWeight M d)
    B hdevT
  have hnext : transformedData.nextBackground =
      gaugeAct (coarseTransform u) originalData.nextBackground := by
    have hbase := cmp99SourceBaseCoarseBackground_gaugeAct u background
    simpa [originalData, transformedData, transformedBackground,
      CMP99PhysicalRegionalScaleData.nextBackground,
      cmp99SourceRegionalScaleDataOfDeviationBudget, hbase] using
      (cmp99PhysicalUbarGaugeConfigOfDeviationBudget_gaugeAct
        u background (cmp99SourceBaseCoarseBackground background)
        (cmp99SourceUbarGamma1 (G := SUN Nc))
        (cmp99SourceUbarGamma2 (G := SUN Nc))
        (cmp99SourceUbarGamma3 (G := SUN Nc)) B hdev hdevT
        (cmp99SourceUbarGamma1_path (G := SUN Nc))
        (cmp99SourceUbarGamma1_end (G := SUN Nc))
        (fun b x _hx => cmp99SourceUbarGamma2_path (G := SUN Nc) b x)
        (cmp99SourceUbarGamma3_path (G := SUN Nc))
        (cmp99SourceUbarGamma3_end (G := SUN Nc)))
  exact CMP99SourceGaugeRegularScalePair.mk
    blockSaturated originalData transformedData rfl rfl hnext

/-- The transformed member of the canonical pair propagates the literal
source radius to the next scale.  This is a derived output of the same Ubar
construction, not a recursive small-field premise supplied by the caller. -/
theorem cmp99SourceGaugeRegularScalePair_transformed_nextBackground_small
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (blockSaturated : Omega.BlockSaturated)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (epsilon : ℝ) (epsilon_nonneg : 0 ≤ epsilon)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilon <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall : cmp99UbarLogRadius
      (cmp99SourceUbarFineNoWindingBudget epsilon noWinding) < 1)
    (transformedSmall : ∀ e : ConcreteEdge d (M * N'),
      ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        epsilon)
    (e : ConcreteEdge d N') :
    ‖(((cmp99SourceGaugeRegularScalePair hd hM Omega background
          blockSaturated u epsilon epsilon_nonneg noWinding transformedSmall)
        .transformedData.nextBackground e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilon := by
  have h :=
    norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
      hd hM Omega (gaugeAct u background)
      (cmp99SourceBlockAverageWeight M d) epsilon epsilon_nonneg noWinding
      logSmall transformedSmall e
  simpa [cmp99SourceGaugeRegularScalePair,
    cmp99SourceRegionalScaleDataOfFineSmall] using h

end

end YangMills.RG
