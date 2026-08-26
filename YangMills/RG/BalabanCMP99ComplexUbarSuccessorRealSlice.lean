import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice
import YangMills.RG.BalabanCMP99ComplexLocalizedUbarBackground
import YangMills.RG.BalabanCMP99SourceRegionalScale

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# The complex Ubar successor restricts to the canonical physical successor

The analytic recursion advances every coarse bond.  Its compact real slice
therefore agrees with the canonical global physical Ubar successor, not with
the localized successor that is deliberately set to one outside a retained
carrier.  This file states that distinction in the type.

The complex and physical no-winding budgets may use different conservative
radii.  They occur only in proof arguments: after coercion, both blocks are
the exponential of the same weighted principal-logarithm sum times the same
coarse holonomy.  No equality of budgets is assumed.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The analytic and physical weighted Ubar exponents have the same matrix
on the compact real slice. -/
theorem cmp99UbarSpecialLinearExponent_realSlice
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc) :
    cmp99UbarSpecialLinearExponent s w
        (fun i ↦ cmp99SUNToSpecialLinear Nc (D i)) =
      cmp99UbarSpecialUnitaryExponent s w D := by
  unfold cmp99UbarSpecialLinearExponent
    cmp99UbarSpecialUnitaryExponent cmp99UbarUnitaryExponent
    cmp99UbarExponent
  rfl

/-- Budget proofs do not alter the compact real-slice value of one complete
Ubar block.  The two budgets are intentionally independent. -/
theorem cmp99UbarSpecialLinearBlockOfDeviationBudget_realSlice
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (D : ι → SUN Nc)
    (Bcomplex Bphysical : MatrixNearLogNoWindingBudget Nc)
    (hcomplex : ∀ i ∈ s,
      ‖((cmp99SUNToSpecialLinear Nc (D i) :
          Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ Bcomplex.δ)
    (hphysical : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ Bphysical.δ)
    (coarse : SUN Nc) :
    cmp99UbarSpecialLinearBlockOfDeviationBudget s w
        (fun i ↦ cmp99SUNToSpecialLinear Nc (D i))
        Bcomplex hcomplex (cmp99SUNToSpecialLinear Nc coarse) =
      cmp99SUNToSpecialLinear Nc
        (cmp99UbarSpecialUnitaryBlockOfDeviationBudget
          s w D Bphysical hphysical coarse) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [show
      ((cmp99UbarSpecialLinearBlockOfDeviationBudget s w
          (fun i ↦ cmp99SUNToSpecialLinear Nc (D i))
          Bcomplex hcomplex (cmp99SUNToSpecialLinear Nc coarse) :
            Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
        NormedSpace.exp
            (cmp99UbarSpecialLinearExponent s w
              (fun i ↦ cmp99SUNToSpecialLinear Nc (D i))) *
          (coarse : Matrix (Fin Nc) (Fin Nc) ℂ) by
        rw [cmp99UbarSpecialLinearBlockOfDeviationBudget_coe,
          cmp99SUNToSpecialLinear_coe],
      cmp99SUNToSpecialLinear_coe,
      cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe,
      cmp99UbarSpecialLinearExponent_realSlice]

/-- The straight coarse transport also commutes with the canonical compact
embedding. -/
theorem cmp99SourceBaseCoarseBackground_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    cmp99SourceBaseCoarseBackground
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        (cmp99SourceBaseCoarseBackground U) := by
  have hpos : ∀ b : PhysicalBond d N',
      cmp99SourceBaseCoarseBackground
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
          (positiveEdgeOfPhysicalBond b) =
        cmp99SUNToSpecialLinear Nc
          (cmp99SourceBaseCoarseBackground U
            (positiveEdgeOfPhysicalBond b)) := by
    intro b
    let analytic := cmp99SourceParallelTransportPath
      (G := Matrix.SpecialLinearGroup (Fin Nc) ℂ)
      (blockBasepoint M N' b.1) b.2
    let physical := cmp99SourceParallelTransportPath (G := SUN Nc)
      (blockBasepoint M N' b.1) b.2
    have hedges : analytic.edges = physical.edges := by
      unfold analytic physical cmp99SourceParallelTransportPath
      induction M with
      | zero => rfl
      | succ n ih =>
          simp only [cmp99StraightPositivePath,
            OrientedLatticePath.castEnd_edges,
            OrientedLatticePath.trans]
          rw [ih]
    rw [cmp99SourceBaseCoarseBackground_apply_pos,
      cmp99SourceBaseCoarseBackground_apply_pos]
    unfold OrientedLatticePath.holonomy
    change wilsonLine (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
        analytic.edges =
      cmp99SUNToSpecialLinear Nc (wilsonLine U physical.edges)
    rw [hedges]
    exact
      wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear
        U physical.edges
  apply gaugeConfig_ext
  intro e
  cases e with
  | mk y mu orient =>
      cases orient
      · change
          (cmp99SourceBaseCoarseBackground
            (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
              (positiveEdgeOfPhysicalBond (y, mu)))⁻¹ =
            cmp99SUNToSpecialLinear Nc
              ((cmp99SourceBaseCoarseBackground U
                (positiveEdgeOfPhysicalBond (y, mu)))⁻¹)
        rw [map_inv, hpos]
      · exact hpos (y, mu)

/-- Each literal four-path deviation commutes with the compact embedding. -/
theorem cmp99SourceComplexLocalizedUbarDeviation_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp99SourceComplexLocalizedUbarDeviation
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) b x =
      cmp99SUNToSpecialLinear Nc
        (UbarDeviation U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)) := by
  unfold cmp99SourceComplexLocalizedUbarDeviation UbarDeviation
  dsimp only
  rw [wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear,
    wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear,
    wilsonLine_cmp99PhysicalGaugeBackgroundToSpecialLinear,
    cmp99SourceBaseCoarseBackground_realSlice]
  simp only [cmp99PhysicalGaugeBackgroundToSpecialLinear_apply]
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  apply congrArg
  rfl

/-- One analytic source block is the canonical image of the physical source
block.  In particular, no equality between the complex and physical scalar
budgets is required. -/
theorem cmp99SourceComplexLocalizedUbarBlock_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Bcomplex Bphysical : MatrixNearLogNoWindingBudget Nc)
    (hcomplex : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(@cmp99SourceComplexLocalizedUbarDeviation d M N' Nc _ _ _
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U) b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ Bcomplex.δ)
    (hphysical : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ Bphysical.δ)
    (b : PhysicalBond d N') :
    @cmp99SourceComplexLocalizedUbarBlock d M N' Nc _ _ _ _
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
        Bcomplex hcomplex b =
      cmp99SUNToSpecialLinear Nc
        (cmp99PhysicalUbarBlockOfDeviationBudget
          (d := d) (L := M) (N' := N') (Nc := Nc)
          (A_fine := U)
          (A_coarse := cmp99SourceBaseCoarseBackground U)
          (Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc))
          (Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc))
          (Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc))
          (B := Bphysical) (hdev := hphysical) b) := by
  let D : FinBox d (M * N') → SUN Nc := fun x ↦
    UbarDeviation U (cmp99SourceBaseCoarseBackground U)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b)
  have hD : (fun x ↦ cmp99SourceComplexLocalizedUbarDeviation
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U) b x) =
      fun x ↦ cmp99SUNToSpecialLinear Nc (D x) := by
    funext x
    exact cmp99SourceComplexLocalizedUbarDeviation_realSlice U b x
  unfold cmp99SourceComplexLocalizedUbarBlock
    cmp99PhysicalUbarBlockOfDeviationBudget
  dsimp only
  rw [hD, cmp99SourceBaseCoarseBackground_realSlice]
  exact cmp99UbarSpecialLinearBlockOfDeviationBudget_realSlice
    (blockOf M N' b.1) (fun _ ↦ (M ^ d : ℝ)⁻¹) D
    Bcomplex Bphysical
    (by
      intro x hx
      simpa [D] using hcomplex b x hx)
    (by
      intro x hx
      simpa [D, UbarDeviationLogArg] using hphysical b x hx)
    (cmp99SourceBaseCoarseBackground U
      (positiveEdgeOfPhysicalBond b))

/-- The complete all-bond analytic successor restricts to the complete
canonical physical successor.  This theorem deliberately does not mention
the selected/localized successor, whose values are one outside its carrier. -/
theorem cmp99SourceComplexLocalizedNextBackground_realSlice
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (Bcomplex Bphysical : MatrixNearLogNoWindingBudget Nc)
    (hcomplex : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(@cmp99SourceComplexLocalizedUbarDeviation d M N' Nc _ _ _
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U) b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ Bcomplex.δ)
    (hphysical : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          U (cmp99SourceBaseCoarseBackground U)
          (positiveEdgeOfPhysicalBond b) x
          (cmp99SourceUbarGamma1 (G := SUN Nc) b)
          (cmp99SourceUbarGamma2 (G := SUN Nc) b)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b)‖ ≤ Bphysical.δ) :
    @cmp99SourceComplexLocalizedNextBackground d M N' Nc _ _ _ _
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
        Bcomplex hcomplex =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        (cmp99PhysicalUbarGaugeConfigOfDeviationBudget
          (d := d) (L := M) (N' := N') (Nc := Nc)
          (A_fine := U)
          (A_coarse := cmp99SourceBaseCoarseBackground U)
          (Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc))
          (Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc))
          (Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc))
          (B := Bphysical) (hdev := hphysical)) := by
  apply gaugeConfig_ext
  intro e
  rcases e with ⟨y, mu, orient⟩
  cases orient
  · change
      (@cmp99SourceComplexLocalizedUbarBlock d M N' Nc _ _ _ _
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
          Bcomplex hcomplex (y, mu))⁻¹ =
        cmp99SUNToSpecialLinear Nc
          ((cmp99PhysicalUbarBlockOfDeviationBudget
            (d := d) (L := M) (N' := N') (Nc := Nc)
            (A_fine := U)
            (A_coarse := cmp99SourceBaseCoarseBackground U)
            (Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc))
            (Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc))
            (Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc))
            (B := Bphysical) (hdev := hphysical) (y, mu))⁻¹)
    rw [map_inv,
      cmp99SourceComplexLocalizedUbarBlock_realSlice]
  · change
      @cmp99SourceComplexLocalizedUbarBlock d M N' Nc _ _ _ _
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
          Bcomplex hcomplex (y, mu) =
        cmp99SUNToSpecialLinear Nc
          (cmp99PhysicalUbarBlockOfDeviationBudget
            (d := d) (L := M) (N' := N') (Nc := Nc)
            (A_fine := U)
            (A_coarse := cmp99SourceBaseCoarseBackground U)
            (Γ_1 := cmp99SourceUbarGamma1 (G := SUN Nc))
            (Γ_2 := cmp99SourceUbarGamma2 (G := SUN Nc))
            (Γ_3 := cmp99SourceUbarGamma3 (G := SUN Nc))
            (B := Bphysical) (hdev := hphysical) (y, mu))
    exact cmp99SourceComplexLocalizedUbarBlock_realSlice
      U Bcomplex Bphysical hcomplex hphysical (y, mu)

/-- Source-facing specialization: the complex successor is the compact
image of the canonical physical successor generated by the normalized
fine-small scale package.  The physical deviation budget and all three
contours are discharged by that package; only the independent analytic
deviation certificate remains visible. -/
theorem cmp99SourceComplexLocalizedNextBackground_realSlice_ofFineSmall
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (fineSmall : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (Bcomplex : MatrixNearLogNoWindingBudget Nc)
    (hcomplex : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(@cmp99SourceComplexLocalizedUbarDeviation d M N' Nc _ _ _
          (cmp99PhysicalGaugeBackgroundToSpecialLinear U) b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ Bcomplex.δ) :
    @cmp99SourceComplexLocalizedNextBackground d M N' Nc _ _ _ _
        (cmp99PhysicalGaugeBackgroundToSpecialLinear U)
        Bcomplex hcomplex =
      cmp99PhysicalGaugeBackgroundToSpecialLinear
        ((cmp99SourceRegionalScaleDataOfFineSmall
          (d := d) (M := M) (N' := N') (Nc := Nc) hd hM Omega U
          (cmp99SourceBlockAverageWeight M d) epsilonFine
          epsilonFine_nonneg noWinding fineSmall).nextBackground) := by
  let S := cmp99SourceRegionalScaleDataOfFineSmall
    (d := d) (M := M) (N' := N') (Nc := Nc) hd hM Omega U
    (cmp99SourceBlockAverageWeight M d) epsilonFine
    epsilonFine_nonneg noWinding fineSmall
  exact cmp99SourceComplexLocalizedNextBackground_realSlice U
    Bcomplex S.deviationBudget hcomplex S.deviation_bound

end

end YangMills.RG
