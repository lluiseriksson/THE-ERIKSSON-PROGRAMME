/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99DiagonalFiniteGreenOwnerBound
import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointPhase

/-!
# Fine-to-coarse endpoint displacement and the periodic owner metric

PRE-VALIDATION: source present, `.olean` not yet materialized, and results in
this module are not yet compiler-verified.

The source-separated endpoint carries the literal integer displacement
`x - M*y`. Unit F is written with the shortest periodic displacement from
`x` to the canonical fine block basepoint of `y`. These signed vectors need
not be equal at an even antipodal seam. What is exact, and what the
exponential weight consumes, is equality of their centered `l1` lengths.

This module proves that equality through the common `ZMod` residue and then
transports the sealed diagonal owner-weight estimate. It does not assert a
false signed-vector identity, an interacting Green estimate, regional `B0`,
window-15 attainment or a terminal field.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The literal negative fine-to-coarse endpoint displacement projects to
the periodic difference from the fine target to the canonical block
basepoint of the coarse source. -/
theorem cmp99SourceFineToCoarseEndpointDisplacement_neg_cast
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) (mu : Fin d) :
    (((-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          M x y mu : ℤ) : ZMod (M * N))) =
      ((x mu).val : ZMod (M * N)) -
        (((blockBasepoint M N y) mu).val : ZMod (M * N)) := by
  simp only [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement,
    blockBasepoint]
  push_cast
  ring

/-- Centering the literal endpoint displacement and taking its `l1` length
gives exactly the `l1` length of Unit F's shortest periodic displacement.
Only magnitudes are identified, so the even antipodal sign convention remains
honest. -/
theorem
    cmp89Eq251LatticeL1Length_centered_neg_fineToCoarse_eq_diagonalPeriodic
    {d M N : ℕ} [NeZero M] [NeZero N]
    (x : FinBox d (M * N)) (y : FinBox d N) :
    cmp89Eq251LatticeL1Length
        (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M x y mu)) =
      cmp89Eq251LatticeL1Length
        (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y)) := by
  unfold cmp89Eq251LatticeL1Length
  apply Finset.sum_congr rfl
  intro mu _
  congr 1
  have hcenter :=
    cmp99CenteredPeriodicEndpointRepresentative_natAbs_eq_valMinAbs
      (M * N)
      (-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu)
  change
    (cmp99CenteredPeriodicEndpointRepresentative (M * N)
        (-cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
          M x y mu)).1.natAbs =
      (cmp99DiagonalPeriodicDisplacement
        x (blockBasepoint M N y) mu).natAbs
  rw [hcenter]
  unfold cmp99DiagonalPeriodicDisplacement
  unfold cmp116CMP89PeriodicCoordinateDisplacement
  exact congrArg (fun z : ZMod (M * N) => z.valMinAbs.natAbs)
    (cmp99SourceFineToCoarseEndpointDisplacement_neg_cast x y mu)

/-- The signed-lattice weight of the literal source-separated endpoint is
exactly the weight of the diagonal periodic displacement. -/
theorem
    cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_eq_diagonalPeriodic
    {d M N : ℕ} [NeZero M] [NeZero N]
    (delta : ℝ) (x : FinBox d (M * N)) (y : FinBox d N) :
    cmp89SignedLatticeL1ExponentialWeight delta
        (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M x y mu)) =
      cmp89SignedLatticeL1ExponentialWeight delta
        (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y)) := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  change
    Real.exp (-delta * cmp89Eq251LatticeL1Length
      (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
        (fun mu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y mu))) =
      Real.exp (-delta * cmp89Eq251LatticeL1Length
        (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y)))
  rw [
    cmp89Eq251LatticeL1Length_centered_neg_fineToCoarse_eq_diagonalPeriodic]

/-- Unit F's periodic owner estimate in the literal source-separated endpoint
coordinates. The owner on the source side simplifies to the actual coarse
site `y`, not a separately chosen readout. -/
theorem cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_le_owner
    {M N : ℕ} [NeZero M] [NeZero N]
    {rho : ℝ} (hrho : 0 ≤ rho)
    (x : FinBox 4 (M * N)) (y : FinBox 4 N) :
    cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M x y mu)) ≤
      Real.exp (2 * rho) *
        Real.exp (-rho *
          (finBoxDist (blockSite M N x) y : ℝ)) := by
  calc
    cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
          (fun mu =>
            -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
              M x y mu)) =
      cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y)) :=
      cmp89SignedLatticeL1ExponentialWeight_centered_neg_fineToCoarse_eq_diagonalPeriodic
        (rho / (M : ℝ)) x y
    _ = cmp89SignedLatticeL1ExponentialWeight (rho / (M : ℝ))
        (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
          (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y))) := by
      rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
        cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
      change
        Real.exp (-(rho / (M : ℝ)) * cmp89Eq251LatticeL1Length
          (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y))) =
        Real.exp (-(rho / (M : ℝ)) * cmp89Eq251LatticeL1Length
          (cmp99CenteredPeriodicEndpointVectorRepresentative (M * N)
            (cmp99DiagonalPeriodicDisplacement x (blockBasepoint M N y))))
      rw [
        cmp89Eq251LatticeL1Length_centeredDiagonalPeriodicDisplacement_eq]
    _ ≤ Real.exp (2 * rho) *
        Real.exp (-rho * (finBoxDist (blockSite M N x) y : ℝ)) := by
      simpa using
        (cmp89SignedLatticeL1ExponentialWeight_centeredDiagonal_le_owner
          hrho x (blockBasepoint M N y))

end

end YangMills.RG
