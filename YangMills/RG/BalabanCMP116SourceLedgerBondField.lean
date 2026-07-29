/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq222CutoffSupportInteraction
import YangMills.RG.BalabanCMP116SourcePhysicalContourPotential

/-!
# Literal bond field in the reindexed CMP116 ledger

The source large-field cutoff is naturally written on physical bonds, while
the terminal equation-(2.26) ledger is indexed by `Cube d L`.  The certified
dictionary maps every scalar ledger coordinate to a physical bond coordinate
without mixing ledger cubes.

This module installs the literal Lie-coordinate field on each ledger cube and
proves its selected energy is bounded by the canonical physical localization
projector whenever the physical bonds lying over the selected cubes are
localization-admissible.  Thus the equation-(2.22) energy producer has exactly
the index type consumed by `CMP116Eq226PhysicalContourTermSource`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- The literal `su(Nc)` coordinate field carried by one CMP116 ledger cube. -/
noncomputable def cmp116SourceLedgerCoordinateCochain
    {d L Nc : ℕ}
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1))
    (q : Cube d L) : SUNLieCoord Nc :=
  PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars fun a => b (q, a)

@[simp]
theorem cmp116SourceLedgerCoordinateCochain_apply
    {d L Nc : ℕ}
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1))
    (q : Cube d L) (a : Fin (Nc ^ 2 - 1)) :
    PhysicalGaugeCMP116Dictionary.sunLieCoordScalar
        (cmp116SourceLedgerCoordinateCochain b q) a =
      b (q, a) := by
  simp [cmp116SourceLedgerCoordinateCochain]

/-- Scalar coordinates whose ledger cube belongs to the selected large-field
set. -/
noncomputable def cmp116SourceLedgerSelectedCoordinates
    {d L lieDim : ℕ} (P : Finset (Cube d L)) :
    Finset (CMP116CoordIndex d L lieDim) := by
  classical
  exact P ×ˢ Finset.univ

@[simp]
theorem mem_cmp116SourceLedgerSelectedCoordinates_iff
    {d L lieDim : ℕ} (P : Finset (Cube d L))
    (qa : CMP116CoordIndex d L lieDim) :
    qa ∈ cmp116SourceLedgerSelectedCoordinates P ↔ qa.1 ∈ P := by
  classical
  simp [cmp116SourceLedgerSelectedCoordinates]

/-- Source admissibility of the physical bonds lying over `P` places every
selected ledger coordinate inside the physical localization projector. -/
theorem cmp116SourceLedgerSelectedCoordinates_subset_physicalLocalizedCoordinates
    {d M N' Nc L : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero (Nc ^ 2 - 1)]
    (Dict : PhysicalGaugeCMP116Dictionary
      d (M * N') Nc d L (Nc ^ 2 - 1))
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (Cube d L)}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible
      Dset (Dict.physicalBondsOfCells P) Z0) :
    cmp116SourceLedgerSelectedCoordinates P ⊆
      Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0 := by
  intro qa hqa
  rw [Dict.mem_cmp116Eq223PhysicalLocalizedCoordinates_iff]
  apply hZ0.2
  rw [Dict.mem_physicalBondsOfCells]
  rw [Dict.coordEquiv_cell]
  exact
    (mem_cmp116SourceLedgerSelectedCoordinates_iff P qa).mp hqa

/-- Exact flattening of the selected ledger-bond energy. -/
theorem sum_norm_sq_cmp116SourceLedgerCoordinateCochain
    {d L Nc : ℕ}
    (P : Finset (Cube d L))
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1)) :
    (∑ q ∈ P, ‖cmp116SourceLedgerCoordinateCochain b q‖ ^ 2) =
      ∑ qa ∈ cmp116SourceLedgerSelectedCoordinates P, b qa ^ 2 := by
  classical
  have hq :
      ∀ q : Cube d L,
        ‖cmp116SourceLedgerCoordinateCochain b q‖ ^ 2 =
          ∑ a : Fin (Nc ^ 2 - 1), b (q, a) ^ 2 := by
    intro q
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [cmp116SourceLedgerCoordinateCochain,
      PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars]
  rw [Finset.sum_congr rfl fun q _ => hq q]
  rw [cmp116SourceLedgerSelectedCoordinates, Finset.sum_product]

/-- The selected literal ledger energy is bounded by the canonical physical
localization quadratic form.  This is the source producer for the
`cutoff_energy_bound` field. -/
theorem sum_norm_sq_cmp116SourceLedgerCoordinateCochain_le_dotProduct
    {d M N' Nc L : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero (Nc ^ 2 - 1)]
    (Dict : PhysicalGaugeCMP116Dictionary
      d (M * N') Nc d L (Nc ^ 2 - 1))
    {Dset : Finset (Finset (FinBox d N'))}
    {P : Finset (Cube d L)}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : CMP116LocalizationAdmissible
      Dset (Dict.physicalBondsOfCells P) Z0)
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1)) :
    (∑ q ∈ P, ‖cmp116SourceLedgerCoordinateCochain b q‖ ^ 2) ≤
      b ⬝ᵥ
        Matrix.mulVec
          (cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0)) b := by
  rw [sum_norm_sq_cmp116SourceLedgerCoordinateCochain]
  rw [Dict.dotProduct_physicalLocalizationProjection_mulVec]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (cmp116SourceLedgerSelectedCoordinates_subset_physicalLocalizedCoordinates
      Dict hZ0)
    (by
      intro qa hqa hnot
      positivity)

namespace CMP116Eq214PhysicalContourDensity

/-- Install the literal ledger-indexed bond field without altering the
contour, Gaussian, or potential data. -/
def withSourceLedgerBondField
    {nDelta nY d L Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero L]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ) :
    CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1) where
  spectatorSupport := C.spectatorSupport
  fluctuationSupport := C.fluctuationSupport
  deltaRadius := C.deltaRadius
  yRadius := C.yRadius
  referenceRoot := C.referenceRoot
  baseGamma := C.baseGamma
  contourGamma := C.contourGamma
  baseCovariance := C.baseCovariance
  contourCovariance := C.contourCovariance
  basePrecision := C.basePrecision
  contourPrecision := C.contourPrecision
  determinantDensity := C.determinantDensity
  potential := C.potential
  bondField := fun b q => cmp116SourceLedgerCoordinateCochain b q
  threshold := threshold
  contourGamma_zero := C.contourGamma_zero
  contourCovariance_zero := C.contourCovariance_zero
  contourPrecision_zero := C.contourPrecision_zero
  determinantDensity_zero := C.determinantDensity_zero
  determinantDensity_sq_mul_basePrecision_det :=
    C.determinantDensity_sq_mul_basePrecision_det
  potential_zero := C.potential_zero

@[simp]
theorem withSourceLedgerBondField_bondField
    {nDelta nY d L Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero L]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1))
    (q : Cube d L) :
    (C.withSourceLedgerBondField threshold).bondField b q =
      cmp116SourceLedgerCoordinateCochain b q := by
  rfl

@[simp]
theorem withSourceLedgerBondField_threshold
    {nDelta nY d L Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero L]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ) :
    (C.withSourceLedgerBondField threshold).threshold = threshold := by
  rfl

/-- The installed field is the same literal field seen by the small-field
cutoff.  Hence nonvanishing of the complete cutoff gives the strict threshold
bound needed by the radial cubic estimate; the energy producer above and the
cutoff-support producer cannot drift to different fields. -/
theorem withSourceLedgerBondField_norm_lt_of_cutoffFactor_ne_zero
    {nDelta nY d L Nc : ℕ}
    {Site : Type*} {Psi Phi : Site → Type*}
    [NeZero L]
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      (Cube d L) Site Psi Phi (SUNLieCoord Nc) (Nc ^ 2 - 1))
    (threshold : ℝ)
    (Y0 P : Finset (Cube d L))
    (b : CMP116Eq214GaussianCoordinate (Cube d L) (Nc ^ 2 - 1))
    (hcutoff :
      (((C.withSourceLedgerBondField threshold).toLocalFiniteGaussianData
          ).toLocalAnalyticData.toAnalyticData.cutoffFactor Y0 P b) ≠ 0)
    {q : Cube d L} (hq : q ∈ Y0) :
    ‖cmp116SourceLedgerCoordinateCochain b q‖ < threshold := by
  let A :=
    ((C.withSourceLedgerBondField threshold).toLocalFiniteGaussianData
      ).toLocalAnalyticData.toAnalyticData
  have h := A.norm_bondField_lt_threshold_of_cutoffFactor_ne_zero
    Y0 P b hcutoff hq
  exact h

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
