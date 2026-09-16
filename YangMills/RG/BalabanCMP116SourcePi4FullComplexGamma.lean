/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2
import YangMills.RG.BalabanCMP116Eq214Interior
import YangMills.RG.BalabanCMP96ConstraintElimination

/-!
# Literal full-source complex Gamma and `R3`

The positive reference Gaussian in CMP116 is fixed at the real fully coupled
point.  Consequently its physical covariance root is real and fixed while
the source weakening variables deform the precision inside

`Gamma_sigma = C_elimᵀ K_sigma (C_elim P_(Z0^c)) S0`.

This module implements that printed ordering directly on the scalar
bond--Lie coordinates.  It deliberately uses the analytic transpose, not a
Hermitian adjoint.  The terminal identity derives the literal correction

`R3 = Gamma_sigma - Gamma_0
    = - C_elimᵀ R2 (C_elim P_(Z0^c)) S0`

from the source sign `R2 = K0 - K_sigma`.
-/

namespace YangMills.RG

noncomputable section

open Matrix

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Physical bonds outside the bilateral interior of `Z0`. -/
noncomputable def cmp116SourcePi4ComplementBonds
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (Z0 : Finset (FinBox 4 (2 * Q))) :
    Finset (PhysicalBond 4 (M * (2 * Q))) := by
  classical
  exact Finset.univ.filter fun b => ¬cmp116BondInterior Z0 b

@[simp]
theorem mem_cmp116SourcePi4ComplementBonds_iff
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (b : PhysicalBond 4 (M * (2 * Q))) :
    b ∈ cmp116SourcePi4ComplementBonds Z0 ↔
      ¬cmp116BondInterior Z0 b := by
  simp [cmp116SourcePi4ComplementBonds]

/-- The literal CMP96 constraint-elimination matrix on the coordinates of the
complete source walk. -/
noncomputable def cmp116SourcePi4ConstraintMatrix
    (M Q Nc : ℕ) [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (Nc ^ 2 - 1)] :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (cmp96ConstraintEliminationCLM
      (d := 4) (L := M) (N' := 2 * Q) (Nc := Nc))

/-- The literal complement projection in the same physical scalar
coordinates. -/
noncomputable def cmp116SourcePi4ComplementProjectionMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (Z0 : Finset (FinBox 4 (2 * Q))) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix
    (physicalBondProjection
      (cmp116SourcePi4ComplementBonds (M := M) Z0))

/-- Fixed real physical Gaussian root, embedded canonically into the complex
source coordinates. -/
noncomputable def cmp116SourcePi4ReferenceRootMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (root : PhysicalEndomorphism M Q Nc) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116PhysicalEndomorphismComplexMatrix root

/-- Literal full-source complex Gamma in the printed CMP116 ordering. -/
noncomputable def cmp116SourcePi4FullComplexGammaMatrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  Matrix.transpose (cmp116SourcePi4ConstraintMatrix M Q Nc) *
    cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma *
    (cmp116SourcePi4ConstraintMatrix M Q Nc *
      cmp116SourcePi4ComplementProjectionMatrix Z0) *
    cmp116SourcePi4ReferenceRootMatrix root

/-- Fully coupled physical Gamma, with the original physical precision and
the same fixed reference root. -/
noncomputable def cmp116SourcePi4PhysicalBaseGammaMatrix
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    (Z0 : Finset (FinBox 4 (2 * Q))) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  Matrix.transpose (cmp116SourcePi4ConstraintMatrix M Q Nc) *
    cmp116PhysicalEndomorphismComplexMatrix K *
    (cmp116SourcePi4ConstraintMatrix M Q Nc *
      cmp116SourcePi4ComplementProjectionMatrix Z0) *
    cmp116SourcePi4ReferenceRootMatrix root

/-- Literal full-source complex correction `R3 = Gamma_sigma - Gamma_0`. -/
noncomputable def cmp116SourcePi4FullComplexR3Matrix
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    Matrix (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0 sigma -
    cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0

/-- At full coupling the complex Gamma is exactly its physical base value. -/
theorem cmp116SourcePi4FullComplexGammaMatrix_one_eq_physical
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
    cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0 (fun _ => 1) =
      cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0 := by
  unfold cmp116SourcePi4FullComplexGammaMatrix
    cmp116SourcePi4PhysicalBaseGammaMatrix
  rw [cmp116SourcePi4FullComplexWeakenedPrecisionMatrix_one_eq_physical
    anchor K hsourceRange hrange hc hmass hK hD]

/-- Exact source identity for the complex `R3`.  No complex square root is
introduced: the real reference root is fixed and all contour dependence is
carried by the literal precision correction `R2`. -/
theorem cmp116SourcePi4FullComplexR3Matrix_eq_neg_constraint_mul_R2
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0 sigma =
      -(Matrix.transpose (cmp116SourcePi4ConstraintMatrix M Q Nc) *
        cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma *
        (cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix Z0) *
        cmp116SourcePi4ReferenceRootMatrix root) := by
  unfold cmp116SourcePi4FullComplexR3Matrix
    cmp116SourcePi4FullComplexGammaMatrix
    cmp116SourcePi4PhysicalBaseGammaMatrix
    cmp116SourcePi4FullComplexR2Matrix
  noncomm_ring

end

end YangMills.RG
