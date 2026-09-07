/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214Incidence
import YangMills.RG.BalabanCMP89Eq251UnitLatticeHolderNormalization

/-!
# Cold-sealed CMP116 physical bonds as CMP89 unit displacements

Compiler-verified at exact source checkpoint
`2e295053fab0f5efa9b8e0a7521f6897e104e3b2` by cold GitHub Actions run
`31305272865`. Restoration and saving of `.lake/build` were skipped. The focal
completed 8,472 jobs, the audit exited zero, and all six audited declarations
use only the allowed set `[propext, Classical.choice, Quot.sound]`.

The CMP89 stabilized endpoint split uses

`holder = source - target`.

A positively oriented CMP116 physical bond therefore gives the signed lattice
displacement `-e_dir`, not `+e_dir`.  Canonical representatives of the two
periodic endpoints cannot be subtracted directly: at the periodic seam their
difference is `N - 1`.  This file instead constructs an unwrapped target lift
by adding one in the bond direction before projection modulo `N`.  Both lifts
are proved to project to the literal CMP116 endpoints, and their difference is
proved to be the signed unit edge required by CMP89.

Honest scope: this dictionary constructs only the Holder displacement of a
physical bond.  It does not choose a lift of the localization owner, construct
the transport displacement, bound either endpoint integrand, produce `B0`,
attain window 15, discharge terminal fields, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinatewise projection of a natural lattice lift to the periodic
`FinBox`. -/
def cmp116CMP89NatSiteProjection {d N : ℕ} [NeZero N]
    (x : Fin d → ℕ) : FinBox d N :=
  fun mu ↦ ⟨x mu % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- Canonical natural lift of the source endpoint. -/
def cmp116CMP89PhysicalBondSourceNatLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) : Fin d → ℕ :=
  fun mu ↦ (cmp116BondSource b mu).val

/-- Seam-safe natural lift of the target endpoint.  The lift is incremented
before reduction modulo `N`; this is load-bearing at the periodic seam. -/
def cmp116CMP89PhysicalBondTargetNatLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) : Fin d → ℕ :=
  fun mu ↦ (cmp116BondSource b mu).val + if mu = b.2 then 1 else 0

/-- The source lift projects to the literal source endpoint. -/
theorem cmp116CMP89NatSiteProjection_sourceNatLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) :
    cmp116CMP89NatSiteProjection
        (cmp116CMP89PhysicalBondSourceNatLift b) = cmp116BondSource b := by
  funext mu
  apply Fin.ext
  change (cmp116BondSource b mu).val % N = (cmp116BondSource b mu).val
  exact Nat.mod_eq_of_lt (cmp116BondSource b mu).isLt

/-- The unwrapped target lift projects to the literal shifted endpoint,
including when the bond crosses the periodic seam. -/
theorem cmp116CMP89NatSiteProjection_targetNatLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) :
    cmp116CMP89NatSiteProjection
        (cmp116CMP89PhysicalBondTargetNatLift b) = cmp116BondTarget b := by
  funext mu
  apply Fin.ext
  by_cases hmu : mu = b.2
  · subst mu
    simp [cmp116CMP89NatSiteProjection,
      cmp116CMP89PhysicalBondTargetNatLift, cmp116BondSource,
      cmp116BondTarget, FinBox.shift]
  · simp only [cmp116CMP89NatSiteProjection,
      cmp116CMP89PhysicalBondTargetNatLift, cmp116BondSource,
      cmp116BondTarget, FinBox.shift, hmu, if_false, Nat.add_zero]
    exact Nat.mod_eq_of_lt (b.1 mu).isLt

/-- Integer lift of the physical source endpoint. -/
def cmp116CMP89PhysicalBondSourceLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) : Fin d → ℤ :=
  fun mu ↦ cmp116CMP89PhysicalBondSourceNatLift b mu

/-- Seam-safe integer lift of the physical target endpoint. -/
def cmp116CMP89PhysicalBondTargetLift {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) : Fin d → ℤ :=
  fun mu ↦ cmp116CMP89PhysicalBondTargetNatLift b mu

/-- Signed Holder displacement used by the CMP89 endpoint split. -/
def cmp116CMP89PhysicalBondHolderDisplacement {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) : Fin d → ℤ :=
  fun mu ↦ cmp116CMP89PhysicalBondSourceLift b mu -
    cmp116CMP89PhysicalBondTargetLift b mu

/-- The Holder displacement is coordinatewise the negative unit vector in the
positive physical bond direction. -/
theorem cmp116CMP89PhysicalBondHolderDisplacement_apply {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (mu : Fin d) :
    cmp116CMP89PhysicalBondHolderDisplacement b mu =
      if mu = b.2 then -1 else 0 := by
  by_cases hmu : mu = b.2
  · simp [cmp116CMP89PhysicalBondHolderDisplacement,
      cmp116CMP89PhysicalBondSourceLift,
      cmp116CMP89PhysicalBondTargetLift,
      cmp116CMP89PhysicalBondSourceNatLift,
      cmp116CMP89PhysicalBondTargetNatLift, hmu]
  · simp [cmp116CMP89PhysicalBondHolderDisplacement,
      cmp116CMP89PhysicalBondSourceLift,
      cmp116CMP89PhysicalBondTargetLift,
      cmp116CMP89PhysicalBondSourceNatLift,
      cmp116CMP89PhysicalBondTargetNatLift, hmu]

/-- Every literal CMP116 physical bond constructs the named CMP89 unit-edge
condition; the condition is not accepted as an additional hypothesis. -/
theorem cmp116CMP89PhysicalBondHolderDisplacement_unit {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) :
    CMP89Eq251UnitLatticeBondDisplacement
      (cmp116CMP89PhysicalBondHolderDisplacement b) := by
  classical
  unfold CMP89Eq251UnitLatticeBondDisplacement cmp89Eq251LatticeL1Length
  simp_rw [cmp116CMP89PhysicalBondHolderDisplacement_apply]
  rw [Finset.sum_eq_single b.2]
  · norm_num
  · intro mu _ hmu
    simp [hmu]
  · simp

/-- The real `l1` norm of the physical Holder displacement is exactly one. -/
theorem cmp116CMP89PhysicalBondHolderDisplacement_realL1_eq_one {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) :
    cmp89Eq251DisplacementL1
        (cmp89Eq251LatticeDisplacement
          (cmp116CMP89PhysicalBondHolderDisplacement b)) = 1 :=
  cmp89Eq251DisplacementL1_latticeDisplacement_eq_one_of_unit
    (cmp116CMP89PhysicalBondHolderDisplacement_unit b)

/-- Every real Holder power is exactly one for the physical bond dictionary. -/
theorem cmp116CMP89PhysicalBondHolderDisplacement_rpow_eq_one {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (alpha : ℝ) :
    cmp89Eq251EuclideanNorm
        (cmp89Eq251LatticeDisplacement
          (cmp116CMP89PhysicalBondHolderDisplacement b)) ^ alpha = 1 :=
  cmp89Eq251EuclideanNorm_latticeDisplacement_rpow_eq_one_of_unit
    (cmp116CMP89PhysicalBondHolderDisplacement_unit b)

end

end YangMills.RG
