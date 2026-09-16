import YangMills.RG.BalabanCMP99SourceEq395PhysicalFamily
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCHeadFactor

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

theorem test_multiplier_comp_extend
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (f : FinBox d N → ℝ) :
    (finitePiLpScalarMultiplier (g := g) f).comp
        (extendZeroZeroCLM (𝔤 := g) Omega) =
      (extendZeroZeroCLM (𝔤 := g) Omega).comp
        (finitePiLpScalarMultiplier (g := g)
          (fun x : ActiveGaugeRegion.Site Omega => f x.1)) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ Omega.sites <;>
    simp [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
      extendZeroZeroCLM, hx]

theorem test_restrict_comp_multiplier
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) (f : FinBox d N → ℝ) :
    (restrictZeroCLM (𝔤 := g) Omega).comp
        (finitePiLpScalarMultiplier (g := g) f) =
      (finitePiLpScalarMultiplier (g := g)
        (fun x : ActiveGaugeRegion.Site Omega => f x.1)).comp
        (restrictZeroCLM (𝔤 := g) Omega) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [ContinuousLinearMap.comp_apply, finitePiLpScalarMultiplier_apply,
    restrictZeroCLM]

theorem test_norm_extend_le_one
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    ‖extendZeroZeroCLM (𝔤 := g) Omega‖ ≤ 1 := by
  exact opNorm_le_one_of_norm_map_eq _ (norm_extendZeroZeroCLM_eq Omega)

theorem test_norm_restrict_le_one
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    ‖restrictZeroCLM (𝔤 := g) Omega‖ ≤ 1 := by
  rw [cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint]
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact test_norm_extend_le_one Omega

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

noncomputable def testPhysicalHead
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) : CMP99Eq395AmbientOperator Q Nc :=
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let C := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  h * C * h

theorem test_physical_head_eq_extend_local_restrict
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    testPhysicalHead D hpi5 P hM depth hspacing background budget fineSmall
        hsmall cell =
      (extendZeroZeroCLM
        ((D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j))).comp
        (((D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
          (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
          budget fineSmall hsmall).comp
        (restrictZeroCLM
          ((D cell).operatorCoarseRegion (hpi5 cell)
            (cmp99OmegaPi4Index j)))) := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j)
  let Hambient := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let Hlocal := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site Omega =>
      (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell x.1)
  let C := (D cell).generatedPhysicalCoarseCovarianceCoordinates
    (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
    fineSmall hsmall
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  have hHE : Hambient.comp E = E.comp Hlocal := by
    simpa [Hambient, Hlocal, cmp99Eq395PhysicalSmoothMultiplier] using
      test_multiplier_comp_extend (g := SUNLieCoord Nc) Omega
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)
  have hRH : R.comp Hambient = Hlocal.comp R := by
    simpa [Hambient, Hlocal, cmp99Eq395PhysicalSmoothMultiplier] using
      test_restrict_comp_multiplier (g := SUNLieCoord Nc) Omega
        (fun block : FinBox 4 (2 * Q) =>
          (cmp95SourcePeriodicCoarseSquarePartition P Q).value cell block)
  change Hambient.comp ((E.comp (C.comp R)).comp Hambient) =
    E.comp ((Hlocal.comp (C.comp Hlocal)).comp R)
  calc
    _ = Hambient.comp (E.comp ((C.comp R).comp Hambient)) := by
      rw [← ContinuousLinearMap.comp_assoc E (C.comp R) Hambient]
    _ = (Hambient.comp E).comp ((C.comp R).comp Hambient) := by
      exact (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (E.comp Hlocal).comp ((C.comp R).comp Hambient) := by rw [hHE]
    _ = E.comp (Hlocal.comp ((C.comp R).comp Hambient)) := by
      exact ContinuousLinearMap.comp_assoc _ _ _
    _ = E.comp (Hlocal.comp (C.comp (R.comp Hambient))) := by
      rw [ContinuousLinearMap.comp_assoc C R Hambient]
    _ = E.comp (Hlocal.comp (C.comp (Hlocal.comp R))) := by rw [hRH]
    _ = E.comp ((Hlocal.comp (C.comp Hlocal)).comp R) := by
      simp only [ContinuousLinearMap.comp_assoc]

theorem test_norm_physical_head_le_local
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ‖testPhysicalHead D hpi5 P hM depth hspacing background budget fineSmall
        hsmall cell‖ ≤
      ‖(D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
        (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background
        budget fineSmall hsmall‖ := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell) (cmp99OmegaPi4Index j)
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let F := (D cell).generatedCMP95SectionCSourceHeadFactorCoordinates P
    (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
    fineSmall hsmall
  rw [test_physical_head_eq_extend_local_restrict]
  have hE : ‖E‖ ≤ 1 := test_norm_extend_le_one Omega
  have hR : ‖R‖ ≤ 1 := test_norm_restrict_le_one Omega
  have hFR : ‖F.comp R‖ ≤ ‖F‖ := by
    calc
      ‖F.comp R‖ ≤ ‖F‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hR (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  calc
    ‖E.comp (F.comp R)‖ ≤ ‖E‖ * ‖F.comp R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul hE hFR (norm_nonneg _) zero_le_one
    _ = ‖F‖ := one_mul _

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
