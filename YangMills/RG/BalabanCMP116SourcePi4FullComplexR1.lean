/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexGamma

/-!
# Literal full-source complex `R1`

This module forms the source-prescribed covariance sandwich

`R1 = Gamma_sigmaᵀ C_sigma Gamma_sigma - Gamma_0ᵀ C_0 Gamma_0`

from the complete source covariance and the literal Gamma constructed in the
preceding module.  The transpose is analytic and contains no complex
conjugation.

The terminal telescope separates exactly the two already identified contour
defects: `R3 = Gamma_sigma - Gamma_0` and `C_sigma - C_0`.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Physical fully coupled covariance in the scalar coordinates of the
complete source walk. -/
noncomputable def cmp116SourcePi4PhysicalBaseCovarianceMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp116SourcePi4QuotientExactPatchedCovariance K hc hmass hK)

/-- Literal source-complex covariance sandwich correction. -/
noncomputable def cmp116SourcePi4FullComplexR1Matrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  Matrix.transpose
      (cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0 sigma) *
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0 sigma -
    Matrix.transpose
      (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0) *
      cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK *
      cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0

/-- Pure matrix telescope in the exact noncommutative ordering used by `R1`. -/
theorem Matrix.transpose_mul_cov_mul_sub_eq_telescope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G0 G1 C0 C1 : Matrix ι ι ℂ) :
    Matrix.transpose G1 * C1 * G1 -
        Matrix.transpose G0 * C0 * G0 =
      Matrix.transpose (G1 - G0) * C1 * G1 +
        Matrix.transpose G0 * (C1 - C0) * G1 +
        Matrix.transpose G0 * C0 * (G1 - G0) := by
  simp only [Matrix.transpose_sub]
  noncomm_ring

/-- The full source `R1` is exactly the telescope of the literal `R3` and
complete covariance defect. -/
theorem cmp116SourcePi4FullComplexR1Matrix_eq_telescope
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    cmp116SourcePi4FullComplexR1Matrix
        (R := R) anchor K root hc hmass hK Z0 sigma =
      Matrix.transpose
          (cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0 sigma) *
          cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
            (R := R) anchor K hc hmass hK sigma *
          cmp116SourcePi4FullComplexGammaMatrix
            (R := R) anchor K root hc hmass hK Z0 sigma +
        Matrix.transpose
            (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0) *
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK) *
          cmp116SourcePi4FullComplexGammaMatrix
            (R := R) anchor K root hc hmass hK Z0 sigma +
        Matrix.transpose
            (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0) *
          cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK *
          cmp116SourcePi4FullComplexR3Matrix
            (R := R) anchor K root hc hmass hK Z0 sigma := by
  unfold cmp116SourcePi4FullComplexR1Matrix
    cmp116SourcePi4FullComplexR3Matrix
  exact Matrix.transpose_mul_cov_mul_sub_eq_telescope
    (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0)
    (cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0 sigma)
    (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma)

/-- At full coupling the literal source `R1` vanishes against the physical
base covariance and Gamma. -/
theorem cmp116SourcePi4FullComplexR1Matrix_one_eq_zero
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
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
        (R := R) anchor K root hc hmass hK Z0 (fun _ => 1) = 0 := by
  unfold cmp116SourcePi4FullComplexR1Matrix
  rw [
    cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
      anchor K root hsourceRange hrange hc hmass hK hD Z0,
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
      anchor K hsourceRange hrange hc hmass hK hD]
  unfold cmp116SourcePi4PhysicalBaseCovarianceMatrix
  exact sub_self _

end

end YangMills.RG
