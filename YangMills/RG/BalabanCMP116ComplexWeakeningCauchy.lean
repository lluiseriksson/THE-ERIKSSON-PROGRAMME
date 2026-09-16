/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries

/-!
# Embedding the CMP116 Cauchy contour into complex weakening coordinates

The source Cauchy family varies finitely many weakening coordinates and leaves
every other coordinate at the fully coupled center `1`.  This module embeds
those finite coordinates into the physical weakening index and proves that
the shifted source polydisc is sent to the coordinatewise physical polydisc.

Combining that exact embedding with the complex random-walk majorant produces
the recursive Cauchy boundary bound directly.  Coordinates outside the image
carry radius zero, so the result does not assume a fictitious global contour
radius.
-/

namespace YangMills.RG

universe u v

variable {Δ : Type u} {ω : Type v}

/-- Insert the finitely many complex Cauchy variables into the physical
weakening system and leave every other coordinate at the center `1`. -/
noncomputable def cmp116ComplexWeakeningOfContour
    {n : ℕ} (emb : Fin n ↪ Δ) (z : Fin n → ℂ) : Δ → ℂ :=
  Function.extend emb z (fun _ => 1)

/-- Extend the finite source radii by radius zero outside the contour
coordinates. -/
noncomputable def cmp116ComplexContourRadius
    {n : ℕ} (emb : Fin n ↪ Δ) (radius : Fin n → ℝ) : Δ → ℝ :=
  Function.extend emb radius (fun _ => 0)

/-- The finite shifted source polydisc embeds into the physical coordinatewise
shifted weakening polydisc. -/
theorem cmp116ComplexWeakeningOfContour_mem_shiftedPolydisc
    {n : ℕ} (emb : Fin n ↪ Δ) (radius : Fin n → ℝ)
    (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z) :
    cmp116ComplexWeakeningOfContour emb z ∈
      cmp116ComplexShiftedWeakeningPolydisc
        (cmp116ComplexContourRadius emb radius) := by
  intro d
  by_cases hd : ∃ i, emb i = d
  · obtain ⟨i, rfl⟩ := hd
    rw [cmp116ComplexWeakeningOfContour, cmp116ComplexContourRadius,
      emb.injective.extend_apply, emb.injective.extend_apply]
    exact hz i
  · rw [cmp116ComplexWeakeningOfContour, cmp116ComplexContourRadius,
      Function.extend_apply' _ _ _ hd, Function.extend_apply' _ _ _ hd]
    simp

/-- A cap on the finitely many source radii extends to a cap on every physical
weakening coordinate, using `1 ≤ R` outside the contour image. -/
theorem one_add_cmp116ComplexContourRadius_le
    {n : ℕ} (emb : Fin n ↪ Δ) (radius : Fin n → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R) :
    ∀ d, 1 + cmp116ComplexContourRadius emb radius d ≤ R := by
  intro d
  by_cases hd : ∃ i, emb i = d
  · obtain ⟨i, rfl⟩ := hd
    rw [cmp116ComplexContourRadius, emb.injective.extend_apply]
    exact hcap i
  · rw [cmp116ComplexContourRadius, Function.extend_apply' _ _ _ hd]
    simpa using hR

/-- The physical radial majorant supplies the exact Cauchy boundary condition
for the complex weakened random-walk series along the embedded contour. -/
theorem cmp116Eq214CauchyBoundaryBound_of_complexWeakenedRandomWalkSeries
    {n : ℕ} (emb : Fin n ↪ Δ) (radius : Fin n → ℝ)
    (active : ω → Finset Δ) (term : ω → ℂ) (R : ℝ)
    (hR : 1 ≤ R) (hcap : ∀ i, 1 + radius i ≤ R)
    (hmajor : Summable fun walk => R ^ (active walk).card * ‖term walk‖) :
    CMP116Eq214CauchyBoundaryBound n radius
      (fun z => cmp116ComplexWeakenedRandomWalkSeries active term
        (cmp116ComplexWeakeningOfContour emb z))
      (∑' walk, R ^ (active walk).card * ‖term walk‖) := by
  apply cmp116Eq214CauchyBoundaryBound_of_shiftedPolydisc
  intro z hz
  apply norm_cmp116ComplexWeakenedRandomWalkSeries_le_tsum_majorant
    active term (cmp116ComplexWeakeningOfContour emb z)
    (cmp116ComplexContourRadius emb radius) R (zero_le_one.trans hR)
    (cmp116ComplexWeakeningOfContour_mem_shiftedPolydisc emb radius z hz)
    (fun _ d _ =>
      one_add_cmp116ComplexContourRadius_le emb radius R hR hcap d)
    hmajor

end YangMills.RG
