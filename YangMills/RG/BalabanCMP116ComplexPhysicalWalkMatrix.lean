/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexPhysicalWalkKernel

/-!
# Matrix form of the complex CMP116 physical walk kernel

The complex weakening expansion is first constructed coefficient by
coefficient from real physical one-cochain endomorphisms.  This module
assembles those coefficients into the literal matrix convention consumed by
the CMP116 contour density: rows are output coordinates and columns are input
coordinates.

The source Cauchy variables interpolate literally from `0` to `1`.  For a
finite embedded family, parameter zero switches off precisely the embedded
coordinates and leaves every coordinate outside the image equal to `1`.
The contour base matrix records that literal mixed zero/one configuration;
there is no post-hoc translation by `1`.

All analytic estimates remain entrywise.  No ambient matrix norm or
finite-dimensional condition number is introduced.
-/

namespace YangMills.RG

universe u v

set_option synthInstance.maxHeartbeats 800000

/-- The scalar bond--Lie coordinate used by the physical walk matrix. -/
abbrev CMP116PhysicalWalkCoordinate (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N × Fin (Nc ^ 2 - 1)

/-- A real physical one-cochain endomorphism appearing in a patched walk. -/
abbrev CMP116PhysicalWalkEndomorphism
    (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Literal complex matrix of the weakened physical walk.  The row
`(target, output)` is the output coordinate and the column `(source, input)`
is the input coordinate. -/
noncomputable def cmp116ComplexWeakenedPhysicalWalkMatrix
    {Δ : Type u} {ω : Type v} {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Δ → ℂ) :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ :=
  fun row col =>
    cmp116ComplexWeakenedRandomWalkSeries active
      (fun walk => cmp116ComplexPhysicalOperatorCoefficient
        (term walk) col.1 row.1 col.2 row.2)
      sigma

/-- Matrix of the physical walk along the finite CMP116 Cauchy variables. -/
noncomputable def cmp116ComplexPhysicalWalkContourMatrix
    {Δ : Type u} {ω : Type v} {d N Nc n : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (emb : Fin n ↪ Δ)
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (z : Fin n → ℂ) :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ :=
  cmp116ComplexWeakenedPhysicalWalkMatrix active term
    (cmp116ComplexWeakeningOfContour emb z)

/-- Literal base matrix for a finite contour family.  The embedded
coordinates are zero and every coordinate outside the image remains fully
coupled at one. -/
noncomputable def cmp116ComplexPhysicalWalkContourBaseMatrix
    {Δ : Type u} {ω : Type v} {d N Nc n : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (emb : Fin n ↪ Δ)
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc) :
    Matrix (CMP116PhysicalWalkCoordinate d N Nc)
      (CMP116PhysicalWalkCoordinate d N Nc) ℂ :=
  cmp116ComplexPhysicalWalkContourMatrix emb active term 0

/-- Evaluation fixes the row/output and column/input orientation literally. -/
@[simp]
theorem cmp116ComplexWeakenedPhysicalWalkMatrix_apply
    {Δ : Type u} {ω : Type v} {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (sigma : Δ → ℂ)
    (target source : PhysicalBond d N)
    (output input : Fin (Nc ^ 2 - 1)) :
    cmp116ComplexWeakenedPhysicalWalkMatrix active term sigma
        (target, output) (source, input) =
      cmp116ComplexWeakenedRandomWalkSeries active
        (fun walk => cmp116ComplexPhysicalOperatorCoefficient
          (term walk) source target input output)
        sigma :=
  rfl

/-- At the fully coupled point the matrix is the entrywise `tsum` of the
physical walk coefficients. -/
theorem cmp116ComplexWeakenedPhysicalWalkMatrix_one
    {Δ : Type u} {ω : Type v} {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc) :
    cmp116ComplexWeakenedPhysicalWalkMatrix active term (fun _ => 1) =
      fun row col => ∑' walk,
        cmp116ComplexPhysicalOperatorCoefficient
          (term walk) col.1 row.1 col.2 row.2 := by
  funext row col
  exact cmp116ComplexWeakenedRandomWalkSeries_one active
    (fun walk => cmp116ComplexPhysicalOperatorCoefficient
      (term walk) col.1 row.1 col.2 row.2)

/-- Embedding a finite family identically equal to one leaves every physical
weakening coordinate equal to one. -/
@[simp]
theorem cmp116ComplexWeakeningOfContour_one
    {Δ : Type u} {n : ℕ} (emb : Fin n ↪ Δ) :
    cmp116ComplexWeakeningOfContour emb (fun _ => (1 : ℂ)) =
      fun _ => 1 := by
  funext d
  by_cases hd : ∃ i, emb i = d
  · obtain ⟨i, rfl⟩ := hd
    rw [cmp116ComplexWeakeningOfContour, emb.injective.extend_apply]
  · rw [cmp116ComplexWeakeningOfContour,
      Function.extend_apply' _ _ _ hd]

/-- The contour family at zero is definitionally its literal mixed zero/one
base matrix, supplying the future `contourGamma_zero` normalization without
changing the source interpolation variable. -/
@[simp]
theorem cmp116ComplexPhysicalWalkContourMatrix_zero
    {Δ : Type u} {ω : Type v} {d N Nc n : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (emb : Fin n ↪ Δ)
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc) :
    cmp116ComplexPhysicalWalkContourMatrix emb active term 0 =
      cmp116ComplexPhysicalWalkContourBaseMatrix emb active term :=
  rfl

/-- Zeroing weakening coordinates outside `K` restricts every matrix entry
to walks whose active carrier lies in `K`. -/
theorem cmp116ComplexWeakenedPhysicalWalkMatrix_zeroOutside
    {Δ : Type u} {ω : Type v} {d N Nc : ℕ}
    [DecidableEq Δ]
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (K : Finset Δ) :
    cmp116ComplexWeakenedPhysicalWalkMatrix active term
        (fun x => (cmp116WeakeningZeroOutside K x : ℂ)) =
      fun row col => ∑' walk : {walk // active walk ⊆ K},
        cmp116ComplexPhysicalOperatorCoefficient
          (term walk) col.1 row.1 col.2 row.2 := by
  funext row col
  exact cmp116ComplexWeakenedRandomWalkSeries_zeroOutside active
    (fun walk => cmp116ComplexPhysicalOperatorCoefficient
      (term walk) col.1 row.1 col.2 row.2) K

/-- The existing physical radial operator estimate yields the exact Cauchy
boundary certificate for each matrix entry. -/
theorem cmp116Eq214CauchyBoundaryBound_of_complexPhysicalWalkMatrix_entry
    {Δ : Type u} {ω : Type v} {d N Nc n : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (emb : Fin n ↪ Δ) (radius : Fin n → ℝ)
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term walk) :
    CMP116Eq214CauchyBoundaryBound n radius
      (fun z =>
        cmp116ComplexPhysicalWalkContourMatrix emb active term z row col)
      (∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term walk) col.1 row.1 col.2 row.2‖) := by
  simpa [cmp116ComplexPhysicalWalkContourMatrix,
    cmp116ComplexWeakenedPhysicalWalkMatrix] using
    (cmp116Eq214CauchyBoundaryBound_of_physicalWalkKernel
      emb radius active term col.1 row.1 col.2 row.2 R hR hcap hsum)

/-- The literal zero-contour base entry is controlled by the same radial
physical majorant as the contour family.  Thus the future `R3` estimate does
not need a separate base-Gamma hypothesis. -/
theorem norm_cmp116ComplexPhysicalWalkContourBaseMatrix_entry_le
    {Δ : Type u} {ω : Type v} {d N Nc n : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (emb : Fin n ↪ Δ)
    (active : ω → Finset Δ)
    (term : ω → CMP116PhysicalWalkEndomorphism d N Nc)
    (row col : CMP116PhysicalWalkCoordinate d N Nc)
    (R : ℝ) (hR : 1 ≤ R)
    (hsum : Summable fun walk =>
      R ^ (active walk).card • term walk) :
    ‖cmp116ComplexPhysicalWalkContourBaseMatrix
        emb active term row col‖ ≤
      ∑' walk, R ^ (active walk).card *
        ‖cmp116ComplexPhysicalOperatorCoefficient
          (term walk) col.1 row.1 col.2 row.2‖ := by
  have hz :
      CMP116Eq214ShiftedPolydisc n (fun _ => 0) (0 : Fin n → ℂ) := by
    intro i
    simp
  have hmem :=
    cmp116ComplexWeakeningOfContour_mem_shiftedPolydisc
      emb (fun _ => 0) (0 : Fin n → ℂ) hz
  have hmajor :=
    summable_cmp116ComplexPhysicalCoefficient_radialMajorant
      active term col.1 row.1 col.2 row.2 R
      (zero_le_one.trans hR) hsum
  simpa [cmp116ComplexPhysicalWalkContourBaseMatrix,
    cmp116ComplexPhysicalWalkContourMatrix,
    cmp116ComplexWeakenedPhysicalWalkMatrix] using
    (norm_cmp116ComplexWeakenedRandomWalkSeries_le_tsum_majorant
      active
      (fun walk => cmp116ComplexPhysicalOperatorCoefficient
        (term walk) col.1 row.1 col.2 row.2)
      (cmp116ComplexWeakeningOfContour emb (0 : Fin n → ℂ))
      (cmp116ComplexContourRadius emb (fun _ => 0))
      R (zero_le_one.trans hR) hmem
      (fun _ d _ => by
        simpa [cmp116ComplexContourRadius] using hR)
      hmajor)

end YangMills.RG
