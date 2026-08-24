import YangMills.RG.BalabanCMP99SourceUbarLocalDeviationBound
import YangMills.RG.BalabanCMP99SourceSelectedNextBackgroundLocality
import YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Localized source next background

For a finite selected family of coarse bonds, construct the literal source
Ubar block from the exact fine read carrier and put the identity on every
unselected positive bond.  The result is a complete gauge configuration, but
its analytic premise is local.  Its global next-scale smallness follows from
the selected Ubar bound and the identity exterior.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- One literal source Ubar block whose deviation certificate uses only its
exact fine read carrier. -/
noncomputable def cmp99SourceLocalizedUbarBlock
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (b : PhysicalBond d N')
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) : SUN Nc := by
  let B := cmp99SourceUbarFineNoWindingBudget
    (d := d) (M := M) (Nc := Nc) epsilonFine noWinding
  let D : FinBox d (M * N') → SUN Nc := fun x =>
    UbarDeviation background (cmp99SourceBaseCoarseBackground background)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b)
  exact cmp99UbarSpecialUnitaryBlockOfDeviationBudget
    (blockOf M N' b.1) (fun _ => cmp99SourceBlockAverageWeight M d) D B (by
      intro x hx
      simpa [B, D, UbarDeviationLogArg] using
        norm_cmp99SourceUbarDeviationLogArg_le_fineRadius_of_readBonds
          hd hM background epsilonFine epsilonFine_nonneg b fineSmall x hx)
    (cmp99SourceBaseCoarseBackground background
      (positiveEdgeOfPhysicalBond b))

/-- The localized block still represents the literal source Ubar formula. -/
theorem cmp99SourceLocalizedUbarBlock_coe_eq_Ubar
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (b : PhysicalBond d N')
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    (cmp99SourceLocalizedUbarBlock hd hM background epsilonFine
        epsilonFine_nonneg noWinding b fineSmall :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        background (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b)
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) := by
  change NormedSpace.exp
      (∑ x ∈ blockOf M N' b.1,
        cmp99SourceBlockAverageWeight M d • nearLog
          (((UbarDeviation background
            (cmp99SourceBaseCoarseBackground background)
            (positiveEdgeOfPhysicalBond b) x
            (cmp99SourceUbarGamma1 (G := SUN Nc) b)
            (cmp99SourceUbarGamma2 (G := SUN Nc) b)
            (cmp99SourceUbarGamma3 (G := SUN Nc) b) : SUN Nc) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (cmp99SourceBaseCoarseBackground background
          (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ) =
    NormedSpace.exp
      ((M ^ d : ℝ)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          nearLog
            (((UbarDeviation background
              (cmp99SourceBaseCoarseBackground background)
              (positiveEdgeOfPhysicalBond b) x
              (cmp99SourceUbarGamma1 (G := SUN Nc) b)
              (cmp99SourceUbarGamma2 (G := SUN Nc) b)
              (cmp99SourceUbarGamma3 (G := SUN Nc) b) : SUN Nc) :
                Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (cmp99SourceBaseCoarseBackground background
          (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ)
  apply congrArg (fun Z : Matrix (Fin Nc) (Fin Nc) ℂ =>
    NormedSpace.exp Z *
      (cmp99SourceBaseCoarseBackground background
        (positiveEdgeOfPhysicalBond b) : Matrix (Fin Nc) (Fin Nc) ℂ))
  simp only [cmp99SourceBlockAverageWeight]
  exact (Finset.smul_sum
    (r := (M ^ d : ℝ)⁻¹) (s := blockOf M N' b.1)
    (f := fun x => nearLog
      (((UbarDeviation background
        (cmp99SourceBaseCoarseBackground background)
        (positiveEdgeOfPhysicalBond b) x
        (cmp99SourceUbarGamma1 (G := SUN Nc) b)
        (cmp99SourceUbarGamma2 (G := SUN Nc) b)
        (cmp99SourceUbarGamma3 (G := SUN Nc) b) : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1))).symm

/-- The selected local block has the same explicit next-scale radius as the
global source constructor. -/
theorem norm_cmp99SourceLocalizedUbarBlock_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall : cmp99UbarLogRadius
        (cmp99SourceUbarFineNoWindingBudget
          (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (b : PhysicalBond d N')
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    ‖(cmp99SourceLocalizedUbarBlock hd hM background epsilonFine
        epsilonFine_nonneg noWinding b fineSmall :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilonFine := by
  let B := cmp99SourceUbarFineNoWindingBudget
    (d := d) (M := M) (Nc := Nc) epsilonFine noWinding
  let D : FinBox d (M * N') → SUN Nc := fun x =>
    UbarDeviation background (cmp99SourceBaseCoarseBackground background)
      (positiveEdgeOfPhysicalBond b) x
      (cmp99SourceUbarGamma1 (G := SUN Nc) b)
      (cmp99SourceUbarGamma2 (G := SUN Nc) b)
      (cmp99SourceUbarGamma3 (G := SUN Nc) b)
  let S := blockOf M N' b.1
  have hdev : ∀ x ∈ S,
      ‖(D x : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ := by
    intro x hx
    simpa [B, D, UbarDeviationLogArg] using
      norm_cmp99SourceUbarDeviationLogArg_le_fineRadius_of_readBonds
        hd hM background epsilonFine epsilonFine_nonneg b fineSmall x hx
  have hblock := norm_cmp99UbarSpecialUnitaryBlockOfDeviationBudget_sub_one_le
    S (fun _ => cmp99SourceBlockAverageWeight M d) D B hdev
    (fun _ _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg M) d))
    (sum_cmp99SourceBlockAverageWeight_blockOf (M := M) b.1)
    (by simpa [B] using logSmall)
    (cmp99SourceBaseCoarseBackground background
      (positiveEdgeOfPhysicalBond b)) ((M : ℝ) * epsilonFine)
    (norm_cmp99SourceBaseCoarseBackground_sub_one_le_of_readBonds
      background epsilonFine b fineSmall)
  simpa [cmp99SourceLocalizedUbarBlock, S, D, B,
    cmp99SourceUbarNextFineRadius, cmp99UbarExpRadius,
    cmp99UbarLogRadius, cmp99SourceUbarFineNoWindingBudget_delta]
    using hblock

/-- Complete coarse configuration: literal localized Ubar on selected
positive bonds and identity elsewhere. -/
noncomputable def cmp99SourceLocalizedNextBackground
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (coarseBonds : Finset (PhysicalBond d N'))
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine) :
    PhysicalGaugeBackground d N' Nc := by
  classical
  exact gaugeConfigOfPositiveBonds fun b =>
    if hb : b ∈ coarseBonds then
      cmp99SourceLocalizedUbarBlock hd hM background epsilonFine
        epsilonFine_nonneg noWinding b (fun q hq =>
          fineSmall q (Finset.mem_biUnion.mpr ⟨b, hb, hq⟩))
    else 1

@[simp] theorem cmp99SourceLocalizedNextBackground_apply_pos_of_mem
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (coarseBonds : Finset (PhysicalBond d N')) (fineSmall)
    (b : PhysicalBond d N') (hb : b ∈ coarseBonds) :
    cmp99SourceLocalizedNextBackground hd hM background epsilonFine
        epsilonFine_nonneg noWinding coarseBonds fineSmall
        (positiveEdgeOfPhysicalBond b) =
      cmp99SourceLocalizedUbarBlock hd hM background epsilonFine
        epsilonFine_nonneg noWinding b (fun q hq =>
          fineSmall q (Finset.mem_biUnion.mpr ⟨b, hb, hq⟩)) := by
  classical
  rw [cmp99SourceLocalizedNextBackground,
    gaugeConfigOfPositiveBonds_apply_pos, dif_pos hb]

@[simp] theorem cmp99SourceLocalizedNextBackground_apply_pos_of_not_mem
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (coarseBonds : Finset (PhysicalBond d N')) (fineSmall)
    (b : PhysicalBond d N') (hb : b ∉ coarseBonds) :
    cmp99SourceLocalizedNextBackground hd hM background epsilonFine
        epsilonFine_nonneg noWinding coarseBonds fineSmall
        (positiveEdgeOfPhysicalBond b) = 1 := by
  classical
  rw [cmp99SourceLocalizedNextBackground,
    gaugeConfigOfPositiveBonds_apply_pos, dif_neg hb]

/-- Every positive bond of the completed localized background satisfies the
next-scale radius: selected bonds by the source estimate, all others by
identity. -/
theorem norm_cmp99SourceLocalizedNextBackground_apply_pos_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall : cmp99UbarLogRadius
        (cmp99SourceUbarFineNoWindingBudget
          (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (coarseBonds : Finset (PhysicalBond d N'))
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (b : PhysicalBond d N') :
    ‖(cmp99SourceLocalizedNextBackground hd hM background epsilonFine
        epsilonFine_nonneg noWinding coarseBonds fineSmall
        (positiveEdgeOfPhysicalBond b) :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilonFine := by
  classical
  by_cases hb : b ∈ coarseBonds
  · rw [cmp99SourceLocalizedNextBackground_apply_pos_of_mem
      hd hM background epsilonFine epsilonFine_nonneg noWinding
      coarseBonds fineSmall b hb]
    apply norm_cmp99SourceLocalizedUbarBlock_sub_one_le
      hd hM background epsilonFine epsilonFine_nonneg noWinding logSmall b
  · rw [cmp99SourceLocalizedNextBackground_apply_pos_of_not_mem
      hd hM background epsilonFine epsilonFine_nonneg noWinding
      coarseBonds fineSmall b hb]
    rw [show ‖((1 : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ = 0 by simp]
    let B := cmp99SourceUbarFineNoWindingBudget
      (d := d) (M := M) (Nc := Nc) epsilonFine noWinding
    let delta := cmp99SourceUbarFineDeviationRadius d M epsilonFine
    let theta := delta / (1 - delta)
    have hdelta : 0 ≤ delta := by
      dsimp only [delta, cmp99SourceUbarFineDeviationRadius]
      positivity
    have hdelta_lt_one : delta < 1 := by
      simpa only [B, cmp99SourceUbarFineNoWindingBudget_delta, delta] using
        B.δ_lt_one
    have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta_lt_one
    have htheta : 0 ≤ theta := div_nonneg hdelta hdenDelta.le
    have htheta_lt_one : theta < 1 := by
      simpa only [cmp99UbarLogRadius, B,
        cmp99SourceUbarFineNoWindingBudget_delta, theta, delta] using logSmall
    have hdenTheta : 0 < 1 - theta := sub_pos.mpr htheta_lt_one
    unfold cmp99SourceUbarNextFineRadius
    change 0 ≤ theta + theta ^ 2 / (1 - theta) + (M : ℝ) * epsilonFine
    positivity

/-- The completed selected/identity background is globally small at the next
radius, including reversed oriented edges. -/
theorem norm_cmp99SourceLocalizedNextBackground_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall : cmp99UbarLogRadius
        (cmp99SourceUbarFineNoWindingBudget
          (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (coarseBonds : Finset (PhysicalBond d N'))
    (fineSmall : ∀ q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
        (Nc := Nc) coarseBonds,
      ‖(background (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (e : ConcreteEdge d N') :
    ‖(cmp99SourceLocalizedNextBackground hd hM background epsilonFine
        epsilonFine_nonneg noWinding coarseBonds fineSmall e :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceUbarNextFineRadius d M epsilonFine := by
  rcases e with ⟨y, mu, orient⟩
  cases orient with
  | false =>
      rw [cmp99SourceLocalizedNextBackground,
        gaugeConfigOfPositiveBonds_apply_neg]
      exact (norm_sun_inv_sub_one_le _).trans
        (norm_cmp99SourceLocalizedNextBackground_apply_pos_sub_one_le
          hd hM background epsilonFine epsilonFine_nonneg noWinding logSmall
          coarseBonds fineSmall (y, mu))
  | true =>
      exact norm_cmp99SourceLocalizedNextBackground_apply_pos_sub_one_le
        hd hM background epsilonFine epsilonFine_nonneg noWinding logSmall
        coarseBonds fineSmall (y, mu)

end

end YangMills.RG
