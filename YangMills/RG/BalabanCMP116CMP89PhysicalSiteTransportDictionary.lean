/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Data.ZMod.ValMinAbs
import YangMills.RG.BalabanCMP116CMP89PhysicalBondDisplacementDictionary
import YangMills.RG.PhysicalBondDistance

/-!
# PRE-VALIDATION: CMP116/CMP89 fine-site transport dictionary

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

The stabilized CMP89 endpoint split uses the two integer displacements

`holder = source - target`,  `transport = target - y`,

so its first endpoint is exactly `holder + transport = source - y`.  The
physical Holder displacement was constructed in the preceding cold-sealed
dictionary.  This file constructs the missing transport displacement from a
literal fine site `y` using `ZMod.valMinAbs`, proves its periodic projection,
and proves that its real `l1` length is the sum of the coordinatewise torus
distances.  The first endpoint is deliberately defined by integer addition,
not by choosing a second centered representative: centered representatives do
not preserve addition across the periodic seam.

Honest scope: `y` is a fine site.  This file does not identify `y` with a
coarse localization owner, compare fine and owner distances, construct `B0`,
attain window 15, discharge a terminal field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The shortest signed representative of a periodic coordinate difference. -/
def cmp116CMP89PeriodicCoordinateDisplacement {N : ℕ} [NeZero N]
    (target source : Fin N) : ℤ :=
  (((target.val : ZMod N) - (source.val : ZMod N))).valMinAbs

/-- The signed representative projects to the literal periodic difference. -/
theorem cmp116CMP89PeriodicCoordinateDisplacement_cast {N : ℕ} [NeZero N]
    (target source : Fin N) :
    (cmp116CMP89PeriodicCoordinateDisplacement target source : ZMod N) =
      (target.val : ZMod N) - (source.val : ZMod N) := by
  exact ZMod.coe_valMinAbs _

/-- `valMinAbs` has exactly the circular magnitude used by the physical torus
distance. -/
theorem natAbs_valMinAbs_eq_zmodCircVal {N : ℕ} [NeZero N]
    (z : ZMod N) : z.valMinAbs.natAbs = zmodCircVal z := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  unfold zmodCircVal
  by_cases hz : z = 0
  · simp [hz]
  · letI : NeZero z := ⟨hz⟩
    rw [ZMod.val_neg_of_ne_zero]

/-- The absolute value of the signed coordinate representative is exactly the
coordinatewise torus distance. -/
theorem natAbs_cmp116CMP89PeriodicCoordinateDisplacement_eq_finTorusDist
    {N : ℕ} [NeZero N] (target source : Fin N) :
    (cmp116CMP89PeriodicCoordinateDisplacement target source).natAbs =
      finTorusDist target source := by
  unfold cmp116CMP89PeriodicCoordinateDisplacement finTorusDist zmodCircDist
  exact natAbs_valMinAbs_eq_zmodCircVal _

/-- Fine-site transport displacement `target - y` in the CMP89 convention. -/
def cmp116CMP89PhysicalBondTransportDisplacement {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) (y : FinBox d N) : Fin d → ℤ :=
  fun mu ↦ cmp116CMP89PeriodicCoordinateDisplacement
    (cmp116BondTarget b mu) (y mu)

/-- The transport displacement projects coordinatewise to `target - y`. -/
theorem cmp116CMP89PhysicalBondTransportDisplacement_cast {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (y : FinBox d N) (mu : Fin d) :
    (cmp116CMP89PhysicalBondTransportDisplacement b y mu : ZMod N) =
      ((cmp116BondTarget b mu).val : ZMod N) - (y mu).val := by
  exact cmp116CMP89PeriodicCoordinateDisplacement_cast _ _

/-- The natural source lift projects to the physical source in `ZMod`. -/
theorem cmp116CMP89PhysicalBondSourceNatLift_cast {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) (mu : Fin d) :
    (cmp116CMP89PhysicalBondSourceNatLift b mu : ZMod N) =
      (cmp116BondSource b mu).val := by
  rfl

/-- The seam-safe natural target lift projects to the physical target in
`ZMod`. -/
theorem cmp116CMP89PhysicalBondTargetNatLift_cast {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) (mu : Fin d) :
    (cmp116CMP89PhysicalBondTargetNatLift b mu : ZMod N) =
      (cmp116BondTarget b mu).val := by
  have h := congrArg Fin.val
    (congrFun (cmp116CMP89NatSiteProjection_targetNatLift b) mu)
  change cmp116CMP89PhysicalBondTargetNatLift b mu % N =
    (cmp116BondTarget b mu).val at h
  calc
    (cmp116CMP89PhysicalBondTargetNatLift b mu : ZMod N) =
        ((cmp116CMP89PhysicalBondTargetNatLift b mu % N : ℕ) : ZMod N) := by
          symm
          exact ZMod.natCast_mod _ _
    _ = ((cmp116BondTarget b mu).val : ZMod N) := by rw [h]

/-- The already sealed Holder displacement projects to `source - target`. -/
theorem cmp116CMP89PhysicalBondHolderDisplacement_cast {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (mu : Fin d) :
    (cmp116CMP89PhysicalBondHolderDisplacement b mu : ZMod N) =
      ((cmp116BondSource b mu).val : ZMod N) -
        (cmp116BondTarget b mu).val := by
  unfold cmp116CMP89PhysicalBondHolderDisplacement
    cmp116CMP89PhysicalBondSourceLift cmp116CMP89PhysicalBondTargetLift
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    cmp116CMP89PhysicalBondSourceNatLift_cast,
    cmp116CMP89PhysicalBondTargetNatLift_cast]

/-- The first endpoint displacement used by CMP89.  It is defined by the
literal integer identity `holder + transport`, rather than by a second choice
of centered periodic representatives. -/
def cmp116CMP89PhysicalBondFirstEndpointDisplacement {d N : ℕ} [NeZero N]
    (b : PhysicalBond d N) (y : FinBox d N) : Fin d → ℤ :=
  fun mu ↦ cmp116CMP89PhysicalBondHolderDisplacement b mu +
    cmp116CMP89PhysicalBondTransportDisplacement b y mu

/-- The first endpoint projects to the literal periodic difference
`source - y`, including across the seam. -/
theorem cmp116CMP89PhysicalBondFirstEndpointDisplacement_cast {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (y : FinBox d N) (mu : Fin d) :
    (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y mu : ZMod N) =
      ((cmp116BondSource b mu).val : ZMod N) - (y mu).val := by
  unfold cmp116CMP89PhysicalBondFirstEndpointDisplacement
  rw [Int.cast_add, cmp116CMP89PhysicalBondHolderDisplacement_cast,
    cmp116CMP89PhysicalBondTransportDisplacement_cast]
  ring

/-- The transport `l1` length is exactly the sum of coordinatewise physical
torus distances. -/
theorem cmp116CMP89PhysicalBondTransportDisplacement_realL1_eq {d N : ℕ}
    [NeZero N] (b : PhysicalBond d N) (y : FinBox d N) :
    cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondTransportDisplacement b y) =
      ∑ mu, (finTorusDist (cmp116BondTarget b mu) (y mu) : ℝ) := by
  unfold cmp89Eq251LatticeL1Length
  apply Finset.sum_congr rfl
  intro mu _
  congr 1
  exact natAbs_cmp116CMP89PeriodicCoordinateDisplacement_eq_finTorusDist _ _

/-- In four dimensions the transport `l1` length is bounded by four times the
literal fine-site Chebyshev torus distance. -/
theorem cmp116CMP89PhysicalBondTransportDisplacement_realL1_le_four_finBoxDist
    {N : ℕ} [NeZero N] (b : PhysicalBond 4 N) (y : FinBox 4 N) :
    cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondTransportDisplacement b y) ≤
      4 * (finBoxDist (cmp116BondTarget b) y : ℝ) := by
  rw [cmp116CMP89PhysicalBondTransportDisplacement_realL1_eq]
  calc
    (∑ mu, (finTorusDist (cmp116BondTarget b mu) (y mu) : ℝ)) ≤
        ∑ _mu : Fin 4, (finBoxDist (cmp116BondTarget b) y : ℝ) := by
      gcongr with mu
      exact_mod_cast finTorusDist_le_finBoxDist (cmp116BondTarget b) y mu
    _ = 4 * (finBoxDist (cmp116BondTarget b) y : ℝ) := by simp

/-- The first endpoint costs at most one extra lattice edge, with the unit
Holder fact constructed internally from the physical bond. -/
theorem cmp116CMP89PhysicalBondFirstEndpointDisplacement_realL1_le_add_one
    {d N : ℕ} [NeZero N] (b : PhysicalBond d N) (y : FinBox d N) :
    cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) ≤
      cmp89Eq251LatticeL1Length
          (cmp116CMP89PhysicalBondTransportDisplacement b y) + 1 := by
  exact cmp89Eq251LatticeL1Length_add_le_add_one_of_unit
    (cmp116CMP89PhysicalBondHolderDisplacement_unit b)

end

end YangMills.RG
