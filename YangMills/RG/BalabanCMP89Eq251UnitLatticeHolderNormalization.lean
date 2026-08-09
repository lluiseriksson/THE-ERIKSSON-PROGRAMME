/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointRecombination

/-!
# PRE-VALIDATION: unit-lattice normalization for the CMP89 Holder endpoint

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

The endpoint split exposes the factor
`|holder|^(-alpha)` separately on both endpoint terms.  The physical Holder
displacement is one literal lattice edge.  This file proves internally that
the named unit-edge condition already forces both its `l1` length and its
Euclidean norm to equal one.  Consequently every real power in the Holder
normalization is exactly one; no lower norm bound is accepted as an
additional input.

The later physical owner/bond dictionary must still construct the unit-edge
condition from its bond geometry.  This module does not bound either complex
endpoint integrand, construct `B0`, attain window 15, discharge rows 23--24,
or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

private theorem abs_intCast_eq_natAbs (n : ℤ) :
    |(n : ℝ)| = (n.natAbs : ℝ) := by
  rw [← Int.cast_abs]
  exact_mod_cast (Int.abs_eq_natAbs n)

/-- The real `l1` length of an integer displacement is exactly the lattice
length used by the unit-edge predicate. -/
theorem cmp89Eq251DisplacementL1_latticeDisplacement {d : ℕ}
    (u : Fin d → ℤ) :
    cmp89Eq251DisplacementL1 (cmp89Eq251LatticeDisplacement u) =
      cmp89Eq251LatticeL1Length u := by
  unfold cmp89Eq251DisplacementL1 cmp89Eq251LatticeDisplacement
    cmp89Eq251LatticeL1Length
  apply Finset.sum_congr rfl
  intro mu _
  exact abs_intCast_eq_natAbs (u mu)

/-- A unit lattice displacement has real `l1` length exactly one. -/
theorem cmp89Eq251DisplacementL1_latticeDisplacement_eq_one_of_unit
    {d : ℕ} {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    cmp89Eq251DisplacementL1 (cmp89Eq251LatticeDisplacement u) = 1 := by
  rw [cmp89Eq251DisplacementL1_latticeDisplacement]
  exact hunit

/-- The Euclidean momentum square of a unit integer displacement is exactly
one.  Integrality is load-bearing: it turns `sum |u_mu| = 1` into the
coordinatewise identity `|u_mu|^2 = |u_mu|`. -/
theorem cmp89Eq251MomentumSquare_latticeDisplacement_eq_one_of_unit
    {d : ℕ} {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    cmp89Eq251MomentumSquare (cmp89Eq251LatticeDisplacement u) = 1 := by
  have hsumReal :
      (∑ mu, ((u mu).natAbs : ℝ)) = 1 := by
    exact hunit
  have hsumNat : (∑ mu, (u mu).natAbs) = 1 := by
    exact_mod_cast hsumReal
  have hcoord (mu : Fin d) : (u mu).natAbs ≤ 1 := by
    rw [← hsumNat]
    exact Finset.single_le_sum
      (fun nu _ ↦ Nat.zero_le (u nu).natAbs) (Finset.mem_univ mu)
  have hsquareNat : (∑ mu, ((u mu).natAbs ^ 2 : ℕ)) = 1 := by
    calc
      (∑ mu, ((u mu).natAbs ^ 2 : ℕ)) =
          ∑ mu, (u mu).natAbs := by
        apply Finset.sum_congr rfl
        intro mu _
        have hzeroOrOne : (u mu).natAbs = 0 ∨ (u mu).natAbs = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp (hcoord mu)
        rcases hzeroOrOne with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = 1 := hsumNat
  rw [cmp89Eq251MomentumSquare]
  change (∑ mu, ((u mu : ℤ) : ℝ) ^ 2) = 1
  calc
    (∑ mu, ((u mu : ℤ) : ℝ) ^ 2) =
        ∑ mu, (((u mu).natAbs : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro mu _
      calc
        ((u mu : ℤ) : ℝ) ^ 2 = |((u mu : ℤ) : ℝ)| ^ 2 :=
          (sq_abs ((u mu : ℤ) : ℝ)).symm
        _ = (((u mu).natAbs : ℕ) : ℝ) ^ 2 := by
          congr 1
          exact abs_intCast_eq_natAbs (u mu)
    _ = 1 := by exact_mod_cast hsquareNat

/-- A unit integer displacement has Euclidean norm exactly one. -/
theorem cmp89Eq251EuclideanNorm_latticeDisplacement_eq_one_of_unit
    {d : ℕ} {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    cmp89Eq251EuclideanNorm (cmp89Eq251LatticeDisplacement u) = 1 := by
  rw [cmp89Eq251EuclideanNorm,
    cmp89Eq251MomentumSquare_latticeDisplacement_eq_one_of_unit hunit,
    Real.sqrt_one]

/-- The literal Holder normalization on a unit lattice edge is one for every
real exponent. -/
theorem cmp89Eq251EuclideanNorm_latticeDisplacement_rpow_eq_one_of_unit
    {d : ℕ} {alpha : ℝ} {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    cmp89Eq251EuclideanNorm (cmp89Eq251LatticeDisplacement u) ^ alpha = 1 := by
  rw [cmp89Eq251EuclideanNorm_latticeDisplacement_eq_one_of_unit hunit,
    Real.one_rpow]

end

end YangMills.RG
