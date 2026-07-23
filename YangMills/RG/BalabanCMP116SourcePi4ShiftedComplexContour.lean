/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2Norm
import YangMills.RG.BalabanCMP116Eq214CauchyPolydisc

/-!
# The source `Pi^4` contour in zero-based Cauchy coordinates

The literal source weakening variables are normalized at full coupling:
`sigma = 1`.  The equation-(2.14) contour records its reference point at the
zero vector.  This module fixes the dictionary between those conventions:

`sigma_source(d) = 1 + z(e.symm d)`.

Thus `z = 0` is definitionally full coupling.  The three literal source
corrections `R1`, `R2`, and `R3` consequently vanish at the zero Cauchy
coordinate, exactly as required by `CMP116Eq214PhysicalContourDensity`.
-/

namespace YangMills.RG

noncomputable section

open Matrix

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Translate zero-based equation-(2.14) contour coordinates to the literal
source weakening coordinates, whose physical reference value is one. -/
def cmp116SourcePi4ShiftedCoupling
    {n Q : ℕ} (e : Fin n ≃ FinBox 4 (2 * Q))
    (z : Fin n → ℂ) : FinBox 4 (2 * Q) → ℂ :=
  fun d => 1 + z (e.symm d)

@[simp]
theorem cmp116SourcePi4ShiftedCoupling_zero
    {n Q : ℕ} (e : Fin n ≃ FinBox 4 (2 * Q)) :
    cmp116SourcePi4ShiftedCoupling e 0 = fun _ => 1 := by
  funext d
  simp [cmp116SourcePi4ShiftedCoupling]

@[simp]
theorem norm_cmp116SourcePi4ShiftedCoupling_sub_one
    {n Q : ℕ} (e : Fin n ≃ FinBox 4 (2 * Q))
    (z : Fin n → ℂ) (d : FinBox 4 (2 * Q)) :
    ‖cmp116SourcePi4ShiftedCoupling e z d - 1‖ =
      ‖z (e.symm d)‖ := by
  simp [cmp116SourcePi4ShiftedCoupling]

/-- A shifted Cauchy-polydisc certificate gives the exact source deviation
bound after the affine change of coordinates. -/
theorem norm_cmp116SourcePi4ShiftedCoupling_sub_one_le
    {n Q : ℕ} (e : Fin n ≃ FinBox 4 (2 * Q))
    (radius : Fin n → ℝ) (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    (d : FinBox 4 (2 * Q)) :
    ‖cmp116SourcePi4ShiftedCoupling e z d - 1‖ ≤
      1 + radius (e.symm d) := by
  rw [norm_cmp116SourcePi4ShiftedCoupling_sub_one]
  exact hz (e.symm d)

/-- The source coupling itself is bounded on the shifted Cauchy polydisc.
This is the form consumed by the complete complex-walk estimates. -/
theorem norm_cmp116SourcePi4ShiftedCoupling_le
    {n Q : ℕ} (e : Fin n ≃ FinBox 4 (2 * Q))
    (radius : Fin n → ℝ) (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    (d : FinBox 4 (2 * Q)) :
    ‖cmp116SourcePi4ShiftedCoupling e z d‖ ≤
      2 + radius (e.symm d) := by
  calc
    ‖cmp116SourcePi4ShiftedCoupling e z d‖
        ≤ ‖(1 : ℂ)‖ + ‖z (e.symm d)‖ := by
          exact norm_add_le _ _
    _ ≤ 1 + (1 + radius (e.symm d)) := by
          simpa using add_le_add_left (hz (e.symm d)) 1
    _ = 2 + radius (e.symm d) := by ring

/-- The literal source `R1`, expressed in zero-based Cauchy coordinates,
vanishes at the contour origin. -/
theorem cmp116SourcePi4FullComplexR1Matrix_shifted_zero
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (e : Fin n ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (Z0 : Finset (FinBox 4 (2 * Q))) :
    cmp116SourcePi4FullComplexR1Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e 0) = 0 := by
  rw [cmp116SourcePi4ShiftedCoupling_zero]
  exact cmp116SourcePi4FullComplexR1Matrix_one_eq_zero
    anchor K root hsourceRange hrange hc hmass hK hD Z0

/-- The literal source `R2`, expressed in zero-based Cauchy coordinates,
vanishes at the contour origin. -/
theorem cmp116SourcePi4FullComplexR2Matrix_shifted_zero
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (e : Fin n ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK
          (cmp116SourcePi4ShiftedCoupling e 0) = 0 := by
  rw [cmp116SourcePi4ShiftedCoupling_zero]
  unfold cmp116SourcePi4FullComplexR2Matrix
  rw [cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
    anchor K hsourceRange hrange hc hmass hK hD]
  exact sub_self _

/-- The literal source `R3`, expressed in zero-based Cauchy coordinates,
vanishes at the contour origin. -/
theorem cmp116SourcePi4FullComplexR3Matrix_shifted_zero
    {n M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (e : Fin n ≃ FinBox 4 (2 * Q))
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (Z0 : Finset (FinBox 4 (2 * Q))) :
    cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0
          (cmp116SourcePi4ShiftedCoupling e 0) = 0 := by
  rw [cmp116SourcePi4ShiftedCoupling_zero]
  unfold cmp116SourcePi4FullComplexR3Matrix
  rw [cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
    anchor K root hsourceRange hrange hc hmass hK hD Z0]
  exact sub_self _

end

end YangMills.RG
