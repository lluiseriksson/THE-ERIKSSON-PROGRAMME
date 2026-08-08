/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96ConstraintElimination
import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionLipschitz
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The literal CMP109 constraint-correction fixed point

CMP109 equation (1.3.2) uses the sparse right inverse `h` of the flat block
constraint, not the background minimizer `H` of CMP99 equation (3.126).  Its
nonlinear correction is therefore determined by the literal fixed-point
equation

`D = C(A - h D)`.

The repository already contained both physical ingredients:

* `cmp96ConstraintPivotInsertion`, the distinguished-bond realization of
  `h`, with `Q h = I`;
* `cmp102PhysicalNonlinearCorrectionOfBudget`, the nonlinear source
  correction `C`.

This module first proves the missing volume-uniform source-sup norm of `h`,
then applies the existing two-field correction estimate and Banach's theorem.
The contraction constant is generated internally as

`correctionRate * L^(d-1)`.

This is the correction entering
`B' = g_k C B - h D_tilde(g_k C B)`.  It is deliberately kept distinct from
the previously formalized fixed point `D = C(A - H D)`.

Honest scope: this constructs the CMP109 correction field.  It does not yet
construct the nonlinear minimal-orbit map `U_k`, the localized Lemma-1
activities, the residual `V''_k`, or the estimate (1.36).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open YangMills Function

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The sparse CMP109 right inverse has its exact block-scale source-sup
bound, with no factor depending on the periodic volume. -/
theorem cmp98SourceFieldSupNorm_cmp96ConstraintPivotInsertion_le
    (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp98SourceFieldSupNorm
        (cmp96ConstraintPivotInsertion (L := L) D) ≤
      (L : ℝ) ^ (d - 1) * cmp102PhysicalCorrectionSupNorm D := by
  classical
  unfold cmp98SourceFieldSupNorm
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨p, _hp, rfl⟩
  by_cases hpivot : ∃ c : PhysicalBond d N',
      p = cmp96ConstraintPivotBond c
  · obtain ⟨c, rfl⟩ := hpivot
    rw [cmp96ConstraintPivotInsertion_apply_pivot, norm_smul,
      Real.norm_of_nonneg (by positivity :
        0 ≤ (L : ℝ) ^ (d - 1))]
    exact mul_le_mul_of_nonneg_left
      (norm_apply_le_cmp102PhysicalCorrectionSupNorm D c) (by positivity)
  · rw [cmp96ConstraintPivotInsertion_apply_of_not_pivot]
    · simp only [norm_zero]
      exact mul_nonneg (by positivity)
        (cmp102PhysicalCorrectionSupNorm_nonneg D)
    · intro c hpc
      exact hpivot ⟨c, hpc⟩

/-- Linearity of the sparse insertion in the exact orientation used by the
CMP109 correction map. -/
theorem cmp96ConstraintPivotInsertion_sub
    (D₁ D₂ : CoarsePhysicalOneCochain d N' Nc) :
    cmp96ConstraintPivotInsertion (L := L) (D₁ - D₂) =
      cmp96ConstraintPivotInsertion (L := L) D₁ -
        cmp96ConstraintPivotInsertion (L := L) D₂ := by
  change
    cmp96ConstraintPivotInsertionCLM
        (d := d) (L := L) (N' := N') (Nc := Nc) (D₁ - D₂) =
      cmp96ConstraintPivotInsertionCLM
          (d := d) (L := L) (N' := N') (Nc := Nc) D₁ -
        cmp96ConstraintPivotInsertionCLM
          (d := d) (L := L) (N' := N') (Nc := Nc) D₂
  exact map_sub _ _ _

/-- Subtracting two fields shifted by the literal CMP109 right inverse costs
exactly its volume-uniform source-sup scale. -/
theorem cmp98SourceFieldSupNorm_cmp109PivotShift_sub_le
    (A : FinePhysicalOneCochain d L N' Nc)
    (D₁ D₂ : CoarsePhysicalOneCochain d N' Nc) :
    cmp98SourceFieldSupNorm
        ((A - cmp96ConstraintPivotInsertion (L := L) D₁) -
          (A - cmp96ConstraintPivotInsertion (L := L) D₂)) ≤
      (L : ℝ) ^ (d - 1) *
        cmp102PhysicalCorrectionSupNorm (D₂ - D₁) := by
  have hfield :
      (A - cmp96ConstraintPivotInsertion (L := L) D₁) -
          (A - cmp96ConstraintPivotInsertion (L := L) D₂) =
        cmp96ConstraintPivotInsertion (L := L) (D₂ - D₁) := by
    rw [cmp96ConstraintPivotInsertion_sub]
    abel
  rw [hfield]
  exact cmp98SourceFieldSupNorm_cmp96ConstraintPivotInsertion_le (L := L)
    (D₂ - D₁)

/-- Source-domain and self-map data for the CMP109 correction on a closed
coarse sup-norm ball.  It contains chart existence and a self-map budget, but
no Lipschitz estimate, fixed point, or assumed solution. -/
structure CMP109ConstraintCorrectionBallData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ) where
  rho_nonneg : 0 ≤ ρ
  r_nonneg : 0 ≤ r
  s_nonneg : 0 ≤ s
  chartBudget :
    ∀ D : PhysicalGaugeOneCochainSup d N' Nc, ‖D‖ ≤ ρ →
      CMP102PhysicalNonlinearChartBudget U
        (A - cmp96ConstraintPivotInsertion (L := L)
          (physicalGaugeOneCochainSupEquiv.symm D))
  localRadius_eq :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (chartBudget D hD).localNoWinding.δ = r
  relativeRadius_eq :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (chartBudget D hD).relativeNoWinding.δ = s
  correction_self :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (Nc : ℝ) *
          cmp102PhysicalCorrectionSourceBudget
            (A - cmp96ConstraintPivotInsertion (L := L)
              (physicalGaugeOneCochainSupEquiv.symm D)) r ≤ ρ

/-- The literal CMP109 correction map.  Outside its certified ball it is set
to zero; every theorem below concerns the closed ball. -/
noncomputable def cmp109ConstraintCorrectionMap
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (B : CMP109ConstraintCorrectionBallData U A ρ r s)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  if hD : ‖D‖ ≤ ρ then
    physicalGaugeOneCochainSupEquiv
      (cmp102PhysicalNonlinearCorrectionOfBudget U
        (A - cmp96ConstraintPivotInsertion (L := L)
          (physicalGaugeOneCochainSupEquiv.symm D))
        (B.chartBudget D hD))
  else 0

namespace CMP109ConstraintCorrectionBallData

variable
    {U : PhysicalGaugeBackground d (L * N') Nc}
    {A : FinePhysicalOneCochain d L N' Nc}
    {ρ r s : ℝ}
    (B : CMP109ConstraintCorrectionBallData U A ρ r s)

/-- Inside the certified ball the map is the literal nonlinear correction
evaluated at `A - h D`. -/
theorem correctionMap_eq_of_mem
    (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ) :
    cmp109ConstraintCorrectionMap U A ρ r s B D =
      physicalGaugeOneCochainSupEquiv
        (cmp102PhysicalNonlinearCorrectionOfBudget U
          (A - cmp96ConstraintPivotInsertion (L := L)
            (physicalGaugeOneCochainSupEquiv.symm D))
          (B.chartBudget D hD)) := by
  rw [cmp109ConstraintCorrectionMap, dif_pos hD]

/-- The CMP109 correction map preserves its certified closed ball. -/
theorem mapsTo_correctionMap :
    Set.MapsTo
      (cmp109ConstraintCorrectionMap U A ρ r s B)
      {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ}
      {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ} := by
  intro D hD
  change ‖D‖ ≤ ρ at hD
  change ‖cmp109ConstraintCorrectionMap U A ρ r s B D‖ ≤ ρ
  rw [cmp109ConstraintCorrectionMap, dif_pos hD,
    norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  let X :=
    A - cmp96ConstraintPivotInsertion (L := L)
      (physicalGaugeOneCochainSupEquiv.symm D)
  let BD := B.chartBudget D hD
  have hone : |(1 : ℝ)| < BD.radius := by
    simpa using BD.one_lt_radius
  have hX : cmp98SourceFieldSupNorm X ≤ 1 / 2 := by
    simpa [X, BD] using BD.small 1 hone
  have hrX : 1 / 3 + cmp98SourceContourDisplacementBudget X 1 ≤ r := by
    simpa [X, BD, B.localRadius_eq D hD] using BD.localRadius 1 hone
  have hr1 : r < 1 := by
    simpa [← B.localRadius_eq D hD, BD] using
      BD.localNoWinding.δ_lt_one
  have hdev :
      cmp98SourcePhysicalBlockDisplacementBudget X 1 r < 1 := by
    have hle :
        cmp98SourcePhysicalBlockDisplacementBudget X 1 r ≤ s := by
      simpa [X, BD, B.localRadius_eq D hD,
        B.relativeRadius_eq D hD] using BD.relativeRadius 1 hone
    exact hle.trans_lt (by
      simpa [← B.relativeRadius_eq D hD, BD] using
        BD.relativeNoWinding.δ_lt_one)
  have hsource :=
    cmp102PhysicalCorrectionSupNorm_le_sourceBudget
      U X BD.toFieldChart r BD.base hX hrX hr1 hdev
  exact hsource.trans (by
    simpa [X] using B.correction_self D hD)

/-- The constructed physical contraction rate for `D ↦ C(A - hD)`. -/
def contractionRate
    (_B : CMP109ConstraintCorrectionBallData U A ρ r s) : ℝ :=
  cmp102PhysicalCorrectionContractionRate Nc d L r s *
    (L : ℝ) ^ (d - 1)

theorem contractionRate_nonneg : 0 ≤ B.contractionRate := by
  unfold contractionRate
  apply mul_nonneg
  · unfold cmp102PhysicalCorrectionContractionRate
      cmp102SourceCorrectionLinearRate
      cmp102SourceLogCorrectionLinearRate
      cmp102SourceRightVariationLinearRate
    have hR0 := cmp98SourceLogAverageRadius_nonneg r B.r_nonneg
    have hnearR := nearLogDerivativeBudget_nonneg r B.r_nonneg
    have hnearS := nearLogDerivativeBudget_nonneg s B.s_nonneg
    have hexpR := cmp102ExpLipschitzBudget_nonneg r B.r_nonneg
    have hexpLogR :=
      cmp102ExpLipschitzBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hexpHalf :=
      cmp102ExpLipschitzBudget_nonneg (1 / 2) (by norm_num)
    have houter : 0 ≤ cmp98SourceOuterExpNormBudget r := by
      unfold cmp98SourceOuterExpNormBudget
      have hfirst :=
        expDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hR0
      have hsecond :=
        expSecondDerivativeBudget_nonneg
          (cmp98SourceLogAverageRadius r) hR0
      positivity
    positivity
  · positivity

/-- Nonnegativity of the nonlinear-correction factor before multiplication
by the norm of `h`. -/
private theorem correctionContractionRate_nonneg
    (B : CMP109ConstraintCorrectionBallData U A ρ r s) :
    0 ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s := by
  unfold cmp102PhysicalCorrectionContractionRate
    cmp102SourceCorrectionLinearRate
    cmp102SourceLogCorrectionLinearRate
    cmp102SourceRightVariationLinearRate
  have hR0 := cmp98SourceLogAverageRadius_nonneg r B.r_nonneg
  have hnearR := nearLogDerivativeBudget_nonneg r B.r_nonneg
  have hnearS := nearLogDerivativeBudget_nonneg s B.s_nonneg
  have hexpR := cmp102ExpLipschitzBudget_nonneg r B.r_nonneg
  have hexpLogR :=
    cmp102ExpLipschitzBudget_nonneg
      (cmp98SourceLogAverageRadius r) hR0
  have hexpHalf :=
    cmp102ExpLipschitzBudget_nonneg (1 / 2) (by norm_num)
  have houter : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    have hfirst :=
      expDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hsecond :=
      expSecondDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    positivity
  positivity

/-- On the certified ball the literal CMP109 correction map is contracting
with the generated rate. -/
theorem contractingWith_restrict
    (hcontract : B.contractionRate < 1) :
    let K : NNReal := ⟨B.contractionRate, B.contractionRate_nonneg⟩
    ContractingWith K
      ((B.mapsTo_correctionMap).restrict
        (cmp109ConstraintCorrectionMap U A ρ r s B)
        {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ}
        {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ}) := by
  dsimp only
  let K : NNReal := ⟨B.contractionRate, B.contractionRate_nonneg⟩
  constructor
  · exact_mod_cast hcontract
  · apply LipschitzWith.of_dist_le_mul
    intro D₁ D₂
    have hD₁ := D₁.property
    have hD₂ := D₂.property
    change ‖D₁.1‖ ≤ ρ at hD₁
    change ‖D₂.1‖ ≤ ρ at hD₂
    let X₁ :=
      A - cmp96ConstraintPivotInsertion (L := L)
        (physicalGaugeOneCochainSupEquiv.symm D₁.1)
    let X₂ :=
      A - cmp96ConstraintPivotInsertion (L := L)
        (physicalGaugeOneCochainSupEquiv.symm D₂.1)
    let B₁ := B.chartBudget D₁.1 hD₁
    let B₂ := B.chartBudget D₂.1 hD₂
    have hphysical :=
      cmp102PhysicalCorrectionSupNorm_sub_le
        U X₁ X₂ B₁.toFieldChart B₂.toFieldChart r s
        B₁.base
        (by
          have hone : |(1 : ℝ)| < B₁.radius := by
            simpa using B₁.one_lt_radius
          simpa [X₁, B₁] using B₁.small 1 hone)
        (by
          have hone : |(1 : ℝ)| < B₂.radius := by
            simpa using B₂.one_lt_radius
          simpa [X₂, B₂] using B₂.small 1 hone)
        (by
          have hone : |(1 : ℝ)| < B₁.radius := by
            simpa using B₁.one_lt_radius
          simpa [X₁, B₁, B.localRadius_eq D₁.1 hD₁] using
            B₁.localRadius 1 hone)
        (by
          have hone : |(1 : ℝ)| < B₂.radius := by
            simpa using B₂.one_lt_radius
          simpa [X₂, B₂, B.localRadius_eq D₂.1 hD₂] using
            B₂.localRadius 1 hone)
        (by
          simpa [← B.localRadius_eq D₁.1 hD₁, B₁] using
            B₁.localNoWinding.δ_lt_one)
        (by
          have hone : |(1 : ℝ)| < B₁.radius := by
            simpa using B₁.one_lt_radius
          simpa [X₁, B₁, B.localRadius_eq D₁.1 hD₁,
            B.relativeRadius_eq D₁.1 hD₁] using
              B₁.relativeRadius 1 hone)
        (by
          have hone : |(1 : ℝ)| < B₂.radius := by
            simpa using B₂.one_lt_radius
          simpa [X₂, B₂, B.localRadius_eq D₂.1 hD₂,
            B.relativeRadius_eq D₂.1 hD₂] using
              B₂.relativeRadius 1 hone)
        (by
          simpa [← B.relativeRadius_eq D₁.1 hD₁, B₁] using
            B₁.relativeNoWinding.δ_lt_one)
    have hshift :
        cmp98SourceFieldSupNorm (X₁ - X₂) ≤
          (L : ℝ) ^ (d - 1) *
            cmp102PhysicalCorrectionSupNorm
              (physicalGaugeOneCochainSupEquiv.symm D₂.1 -
                physicalGaugeOneCochainSupEquiv.symm D₁.1) := by
      simpa [X₁, X₂] using
        cmp98SourceFieldSupNorm_cmp109PivotShift_sub_le
          (L := L) A
          (physicalGaugeOneCochainSupEquiv.symm D₁.1)
          (physicalGaugeOneCochainSupEquiv.symm D₂.1)
    have hrate :
        0 ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s := by
      exact B.correctionContractionRate_nonneg
    have hcombined :
        cmp102PhysicalCorrectionSupNorm
            (cmp102PhysicalNonlinearCorrectionOfBudget U X₁ B₁ -
              cmp102PhysicalNonlinearCorrectionOfBudget U X₂ B₂) ≤
          (cmp102PhysicalCorrectionContractionRate Nc d L r s *
              (L : ℝ) ^ (d - 1)) *
            cmp102PhysicalCorrectionSupNorm
              (physicalGaugeOneCochainSupEquiv.symm D₂.1 -
                physicalGaugeOneCochainSupEquiv.symm D₁.1) := by
      calc
        _ ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s *
              cmp98SourceFieldSupNorm (X₁ - X₂) := hphysical
        _ ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s *
              ((L : ℝ) ^ (d - 1) *
                cmp102PhysicalCorrectionSupNorm
                  (physicalGaugeOneCochainSupEquiv.symm D₂.1 -
                    physicalGaugeOneCochainSupEquiv.symm D₁.1)) :=
          mul_le_mul_of_nonneg_left hshift hrate
        _ = _ := by ring
    change
      dist
          (cmp109ConstraintCorrectionMap U A ρ r s B D₁.1)
          (cmp109ConstraintCorrectionMap U A ρ r s B D₂.1) ≤
        (K : ℝ) * dist D₁ D₂
    simp only [cmp109ConstraintCorrectionMap,
      dif_pos hD₁, dif_pos hD₂]
    rw [dist_eq_norm, ← map_sub,
      norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
    have hright :
        cmp102PhysicalCorrectionSupNorm
            (physicalGaugeOneCochainSupEquiv.symm D₂.1 -
              physicalGaugeOneCochainSupEquiv.symm D₁.1) =
          dist D₁ D₂ := by
      rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm,
        map_sub]
      simpa [dist_eq_norm] using (norm_sub_rev D₂.1 D₁.1)
    rw [hright] at hcombined
    simpa [K, contractionRate, X₁, X₂, B₁, B₂] using hcombined

/-- Existence and uniqueness of the CMP109 source correction in the certified
ball. -/
theorem existsUnique_constraintCorrection
    (hcontract : B.contractionRate < 1) :
    ∃! D : PhysicalGaugeOneCochainSup d N' Nc,
      ‖D‖ ≤ ρ ∧ cmp109ConstraintCorrectionMap U A ρ r s B D = D := by
  let f := cmp109ConstraintCorrectionMap U A ρ r s B
  let S : Set (PhysicalGaugeOneCochainSup d N' Nc) := {D | ‖D‖ ≤ ρ}
  have hclosed : IsClosed S := isClosed_le continuous_norm continuous_const
  have hcomplete : IsComplete S := hclosed.isComplete
  have hmaps : Set.MapsTo f S S := by
    simpa [f, S] using B.mapsTo_correctionMap
  let K : NNReal := ⟨B.contractionRate, B.contractionRate_nonneg⟩
  have hcontr : ContractingWith K (hmaps.restrict f S S) := by
    simpa [K, f, S] using B.contractingWith_restrict hcontract
  have hzero : (0 : PhysicalGaugeOneCochainSup d N' Nc) ∈ S := by
    simpa [S] using B.rho_nonneg
  have hfinite :
      edist (0 : PhysicalGaugeOneCochainSup d N' Nc) (f 0) ≠ ⊤ :=
    edist_ne_top _ _
  rcases hcontr.exists_fixedPoint' hcomplete hmaps hzero hfinite with
    ⟨D, hDS, hfix, _⟩
  refine ⟨D, ⟨hDS, hfix⟩, ?_⟩
  intro E hE
  have hfixE : IsFixedPt (hmaps.restrict f S S) ⟨E, hE.1⟩ := by
    apply Subtype.ext
    exact hE.2
  have hfixD : IsFixedPt (hmaps.restrict f S S) ⟨D, hDS⟩ := by
    apply Subtype.ext
    exact hfix
  exact congrArg Subtype.val (hcontr.fixedPoint_unique' hfixE hfixD)

/-- The Banach point solves the literal CMP109 equation
`D = C(A - hD)` with its chart generated at the same field. -/
theorem exists_constraintCorrection_physicalEquation
    (hcontract : B.contractionRate < 1) :
    ∃ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      physicalGaugeOneCochainSupEquiv
          (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp96ConstraintPivotInsertion (L := L)
              (physicalGaugeOneCochainSupEquiv.symm D))
            (B.chartBudget D hD)) = D := by
  rcases B.existsUnique_constraintCorrection hcontract with
    ⟨D, ⟨hD, hfix⟩, _⟩
  exact ⟨D, hD, by
    rw [← B.correctionMap_eq_of_mem D hD]
    exact hfix⟩

end CMP109ConstraintCorrectionBallData

end

end YangMills.RG
