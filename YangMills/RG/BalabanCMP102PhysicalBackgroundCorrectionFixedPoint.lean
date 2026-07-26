/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalBackgroundCorrectionLipschitz
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The physical CMP102 background-correction fixed point

This module applies the Banach fixed-point theorem to the literal map

`D ↦ C(A - H D)`

on a closed ball in the source sup norm.  Its contraction constant is
generated internally by the physical CMP102 correction estimate and the
transported source-sup norm of the physical CMP99 minimizer `H`.

The remaining ball data record only the analytic chart domain and the
self-map budget.  They do not contain a Lipschitz estimate, a fixed point,
or an assumed solution of the correction equation.
-/

namespace YangMills.RG

open YangMills Function

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Source-domain and self-map data for the physical CMP102 correction on a
closed coarse sup-norm ball.  The chart packages are generated pointwise
from scalar source budgets; the common radii make the already proved
two-field estimate applicable across the whole ball. -/
structure CMP102PhysicalBackgroundCorrectionBallData
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (ρ r s : ℝ) where
  /-- The common local logarithmic radius is nonnegative. -/
  r_nonneg : 0 ≤ r
  /-- The common normalized block logarithm radius is nonnegative. -/
  s_nonneg : 0 ≤ s
  /-- A source-explicit logarithmic chart at every point of the ball. -/
  chartBudget :
    ∀ D : PhysicalGaugeOneCochainSup d N' Nc, ‖D‖ ≤ ρ →
      CMP102PhysicalNonlinearChartBudget U
        (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
          (physicalGaugeOneCochainSupEquiv.symm D))
  /-- Every local logarithmic chart uses the common radius `r`. -/
  localRadius_eq :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (chartBudget D hD).localNoWinding.δ = r
  /-- Every normalized block logarithm uses the common radius `s`. -/
  relativeRadius_eq :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (chartBudget D hD).relativeNoWinding.δ = s
  /-- The explicit CMP102 source budget maps the ball into itself. -/
  correction_self :
    ∀ (D : PhysicalGaugeOneCochainSup d N' Nc) (hD : ‖D‖ ≤ ρ),
      (Nc : ℝ) *
          cmp102PhysicalCorrectionSourceBudget
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
              (physicalGaugeOneCochainSupEquiv.symm D)) r ≤ ρ

/-- The physical correction map on the whole sup-norm space.  Outside the
certified ball it is set to zero; all mathematical statements below concern
its restriction to the ball. -/
noncomputable def cmp102PhysicalBackgroundCorrectionMap
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (ρ r s : ℝ)
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)
    (D : PhysicalGaugeOneCochainSup d N' Nc) :
    PhysicalGaugeOneCochainSup d N' Nc :=
  if hD : ‖D‖ ≤ ρ then
    physicalGaugeOneCochainSupEquiv
      (cmp102PhysicalNonlinearCorrectionOfBudget U
        (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
          (physicalGaugeOneCochainSupEquiv.symm D))
        (B.chartBudget D hD))
  else 0

namespace CMP102PhysicalBackgroundCorrectionBallData

variable
    {U : PhysicalGaugeBackground d (L * N') Nc}
    {a CP ε : ℝ} {ha : 0 < a}
    {hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP}
    {hε : 0 ≤ ε} {hsmall : PhysicalWilsonSmallBackground U ε}
    {hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP}
    {A : PhysicalGaugeOneCochain d (L * N') Nc}
    {ρ r s : ℝ}
    (B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s)

/-- The physical correction map preserves its certified closed ball. -/
theorem mapsTo_correctionMap :
    Set.MapsTo
      (cmp102PhysicalBackgroundCorrectionMap
        U ha hP hε hsmall hbudget A ρ r s B)
      {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ}
      {D : PhysicalGaugeOneCochainSup d N' Nc | ‖D‖ ≤ ρ} := by
  intro D hD
  change ‖D‖ ≤ ρ at hD
  change
    ‖cmp102PhysicalBackgroundCorrectionMap
      U ha hP hε hsmall hbudget A ρ r s B D‖ ≤ ρ
  rw [cmp102PhysicalBackgroundCorrectionMap, dif_pos hD,
    norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
  let X :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
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

/-- The physical composite contraction rate used by Banach. -/
def contractionRate
    (_B : CMP102PhysicalBackgroundCorrectionBallData
      U ha hP hε hsmall hbudget A ρ r s) : ℝ :=
  cmp102PhysicalCorrectionContractionRate Nc d L r s *
    cmp99SourceEq3126PhysicalHSourceSupNorm
      U ha hP hε hsmall hbudget

/-- The fully constructed physical contraction rate is nonnegative. -/
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
  · exact norm_nonneg _

/-- On the certified ball, the correction map is contracting with its
constructed physical rate. -/
theorem contractingWith_restrict
    (hcontract : B.contractionRate < 1) :
    let K : NNReal :=
      ⟨B.contractionRate, B.contractionRate_nonneg⟩
    ContractingWith K
      ((B.mapsTo_correctionMap).restrict
        (cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s B)
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
      A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D₁.1)
    let X₂ :=
      A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget
        (physicalGaugeOneCochainSupEquiv.symm D₂.1)
    let B₁ := B.chartBudget D₁.1 hD₁
    let B₂ := B.chartBudget D₂.1 hD₂
    have hphysical :=
      cmp102PhysicalBackgroundCorrectionSupNorm_sub_le
        U ha hP hε hsmall hbudget A
        (physicalGaugeOneCochainSupEquiv.symm D₁.1)
        (physicalGaugeOneCochainSupEquiv.symm D₂.1)
        B₁ B₂ r s
        (by simpa [B₁] using B.localRadius_eq D₁.1 hD₁)
        (by simpa [B₂] using B.localRadius_eq D₂.1 hD₂)
        (by simpa [B₁] using B.relativeRadius_eq D₁.1 hD₁)
        (by simpa [B₂] using B.relativeRadius_eq D₂.1 hD₂)
    change
      dist
          (cmp102PhysicalBackgroundCorrectionMap
            U ha hP hε hsmall hbudget A ρ r s B D₁.1)
          (cmp102PhysicalBackgroundCorrectionMap
            U ha hP hε hsmall hbudget A ρ r s B D₂.1) ≤
        (K : ℝ) * dist D₁ D₂
    simp only [cmp102PhysicalBackgroundCorrectionMap,
      dif_pos hD₁, dif_pos hD₂]
    rw [dist_eq_norm,
      ← map_sub,
      norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
    have hright :
        cmp102PhysicalCorrectionSupNorm
            (physicalGaugeOneCochainSupEquiv.symm D₂.1 -
              physicalGaugeOneCochainSupEquiv.symm D₁.1) =
          dist D₁ D₂ := by
      rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm,
        map_sub]
      simpa [dist_eq_norm] using
        (norm_sub_rev D₂.1 D₁.1)
    rw [hright] at hphysical
    simpa [K, contractionRate, X₁, X₂, B₁, B₂] using hphysical

/-- **Existence and uniqueness of the physical CMP102 correction.**  Under
the explicit scalar contraction condition, the source-defined map
`D ↦ C(A - H D)` has exactly one fixed point in the certified sup-norm
ball. -/
theorem existsUnique_backgroundCorrection
    (hρ : 0 ≤ ρ)
    (hcontract : B.contractionRate < 1) :
    ∃! D : PhysicalGaugeOneCochainSup d N' Nc,
      ‖D‖ ≤ ρ ∧
        cmp102PhysicalBackgroundCorrectionMap
          U ha hP hε hsmall hbudget A ρ r s B D = D := by
  let f :=
    cmp102PhysicalBackgroundCorrectionMap
      U ha hP hε hsmall hbudget A ρ r s B
  let S : Set (PhysicalGaugeOneCochainSup d N' Nc) := {D | ‖D‖ ≤ ρ}
  have hclosed : IsClosed S := by
    exact isClosed_le continuous_norm continuous_const
  have hcomplete : IsComplete S := hclosed.isComplete
  have hmaps : Set.MapsTo f S S := by
    simpa [f, S] using B.mapsTo_correctionMap
  let K : NNReal := ⟨B.contractionRate, B.contractionRate_nonneg⟩
  have hcontr :
      ContractingWith K (hmaps.restrict f S S) := by
    simpa [K, f, S] using B.contractingWith_restrict hcontract
  have hzero : (0 : PhysicalGaugeOneCochainSup d N' Nc) ∈ S := by
    simpa [S] using hρ
  have hfinite :
      edist (0 : PhysicalGaugeOneCochainSup d N' Nc) (f 0) ≠ ⊤ :=
    edist_ne_top _ _
  rcases hcontr.exists_fixedPoint' hcomplete hmaps hzero hfinite with
    ⟨D, hDS, hfix, _⟩
  refine ⟨D, ⟨hDS, hfix⟩, ?_⟩
  intro E hE
  have hfixE :
      IsFixedPt (hmaps.restrict f S S) ⟨E, hE.1⟩ := by
    apply Subtype.ext
    exact hE.2
  have hfixD :
      IsFixedPt (hmaps.restrict f S S) ⟨D, hDS⟩ := by
    apply Subtype.ext
    exact hfix
  exact congrArg Subtype.val (hcontr.fixedPoint_unique' hfixE hfixD)

end CMP102PhysicalBackgroundCorrectionBallData

end

end YangMills.RG
