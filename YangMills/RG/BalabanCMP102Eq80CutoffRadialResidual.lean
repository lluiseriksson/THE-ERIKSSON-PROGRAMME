/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CutoffCarrier
import YangMills.RG.BalabanCMP116RadialHessianThirdJet

/-!
# Cutoff control on the physical radial segment

Equation (1.36) is a small-field estimate, whereas the Gaussian coordinate
is unbounded.  The literal CMP116 cutoff resolves this mismatch domain by
domain.  This module proves that the field projected to a selected
equation-(80) domain, and every point of its radial segment from zero, remain
inside the source sup-norm ball on nonzero cutoff support.

The terminal theorem feeds a third-jet bound valid on that ball directly
into the exact cubic radial-residual estimate.  It does not assume global
control in the Gaussian coordinate and does not assert functional locality
of the equation-(80) activity for arbitrary input functions.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open Set
open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- The source sup norm is exactly homogeneous under real scalar
multiplication. -/
theorem cmp98SourceFieldSupNorm_smul
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')] [NeZero Nc]
    (t : ℝ) (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    cmp98SourceFieldSupNorm (t • A) =
      |t| * cmp98SourceFieldSupNorm A := by
  rw [← norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm]
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  rw [norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm]

/-- A source-sup-norm ball is star-shaped about zero. -/
theorem cmp98SourceFieldSupNorm_le_of_mem_segment_zero
    {d M N' Nc : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')] [NeZero Nc]
    (A X : PhysicalGaugeOneCochain d (M * N') Nc)
    (threshold : ℝ)
    (hA : cmp98SourceFieldSupNorm A ≤ threshold)
    (hX : X ∈ segment ℝ (0 : PhysicalGaugeOneCochain d (M * N') Nc) A) :
    cmp98SourceFieldSupNorm X ≤ threshold := by
  rcases hX with ⟨u, t, hu, ht, hut, rfl⟩
  have ht1 : t ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  rw [cmp98SourceFieldSupNorm_smul]
  rw [abs_of_nonneg ht]
  calc
    t * cmp98SourceFieldSupNorm A ≤
        1 * cmp98SourceFieldSupNorm A := by
      exact mul_le_mul_of_nonneg_right ht1
        (cmp98SourceFieldSupNorm_nonneg A)
    _ ≤ threshold := by simpa using hA

/-- On nonzero literal cutoff support, every point of the radial segment of
the field projected to a selected equation-(80) domain remains in the
printed source small-field ball. -/
theorem cmp98SourceFieldSupNorm_eq80DomainProjection_segment_le_threshold_of_cutoffFactor_ne_zero
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))] [NeZero Nc]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (hW : W ∈ D)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (X : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
    (hX : X ∈ segment ℝ
      (0 : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc)
      (physicalBondProjection
        (cmp102Eq80SourcePi4LocalizationDomain
          (M := M) anchor W).bondSupport
        (cmp116SourcePhysicalCoordinateCochain b))) :
    cmp98SourceFieldSupNorm X ≤ threshold := by
  apply cmp98SourceFieldSupNorm_le_of_mem_segment_zero
    (physicalBondProjection
      (cmp102Eq80SourcePi4LocalizationDomain
        (M := M) anchor W).bondSupport
      (cmp116SourcePhysicalCoordinateCochain b))
    X threshold
  · exact
      cmp98SourceFieldSupNorm_eq80DomainProjection_le_threshold_of_cutoffFactor_ne_zero
        anchor D W hW P threshold b hthreshold hcutoff
  · exact hX

/-- A third-jet estimate required only on the source small-field ball yields
the exact cubic residual estimate for the literal field projected to one
selected equation-(80) domain.  The cutoff constructs every radial-segment
premise internally. -/
theorem abs_half_inner_cmp116RadialTaylorResidualOperator_eq80DomainProjection_le_of_cutoff
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (D : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (W : CMP102Eq80SourcePi4PhysicalDomainLabel anchor)
    (hW : W ∈ D)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hthreshold : 0 ≤ threshold)
    (hcutoff :
      (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor D)
            threshold (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff P threshold
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (f : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc → ℝ)
    (hf : ContDiff ℝ 3 f)
    (Λ : ℝ)
    (hthird : ∀ X,
      cmp98SourceFieldSupNorm X ≤ threshold →
        ‖iteratedFDeriv ℝ 3 f X‖ ≤ Λ) :
    let B :=
      physicalBondProjection
        (cmp102Eq80SourcePi4LocalizationDomain
          (M := M) anchor W).bondSupport
        (cmp116SourcePhysicalCoordinateCochain b)
    |(1 / 2 : ℝ) * inner ℝ B
        (cmp116RadialTaylorResidualOperator
          f B (hf.of_le (by norm_num)) B)| ≤
      (Λ / 6) * ‖B‖ ^ 3 := by
  dsimp only
  refine
    abs_half_inner_cmp116RadialTaylorResidualOperator_le_of_thirdJet
      f _ hf Λ ?_
  intro X hX
  apply hthird X
  exact
    cmp98SourceFieldSupNorm_eq80DomainProjection_segment_le_threshold_of_cutoffFactor_ne_zero
      anchor D W hW P threshold b hthreshold hcutoff X hX

end

end YangMills.RG
