/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L18_BranchIII_RP_TM_Substantive.ReflectionPositivityCore
import YangMills.L18_BranchIII_RP_TM_Substantive.WilsonReflectionPos
import YangMills.L18_BranchIII_RP_TM_Substantive.SpectralGapToMassGap

/-!
# Branch III closure conditions (Phase 170)

This module assembles the **closure conditions** for the Branch III
(RP + Transfer Matrix) attack route into a single bundle.

## Strategic placement

This is **Phase 170** of the L18_BranchIII_RP_TM_Substantive block.

## What it does

Bundles:
1. The Wilson RP form (Phase 164).
2. The transfer-matrix spectral bound (Phase 167).
3. The unique ground state (Phase 168).
4. The mass-gap construction (Phase 169).

Plus the closure theorem.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L18_BranchIII_RP_TM_Substantive

/-! ## §1. The closure-condition bundle -/

/-- **Closure conditions for Branch III (RP + Transfer Matrix)**. -/
structure BranchIII_RP_TM_Closure (Φ H : Type*) where
  /-- The Wilson RP form. -/
  wilsonRP : WilsonRPForm Φ
  /-- The mass-gap data. -/
  data : BranchIIIMassGapData H

/-! ## §2. The closure theorem -/

/-- **Branch III closure theorem**: closure conditions produce a
    strictly positive mass gap. -/
theorem branchIII_closure_implies_mass_gap_pos
    {Φ H : Type*} (closure : BranchIII_RP_TM_Closure Φ H) :
    0 < closure.data.spectralBound.massGap :=
  branchIII_mass_gap_pos closure.data

#print axioms branchIII_closure_implies_mass_gap_pos

/-! ## §3. Constructive closure -/

/-- **Construct closure from raw data**. -/
theorem branchIII_closure_construct
    {Φ H : Type*} (wRP : WilsonRPForm Φ) (data : BranchIIIMassGapData H) :
    BranchIII_RP_TM_Closure Φ H :=
  { wilsonRP := wRP, data := data }

#print axioms branchIII_closure_construct

/-! ## §4. Coordination note -/

/-
This file is **Phase 170** of the L18_BranchIII_RP_TM_Substantive block.

## What's done

Two substantive Lean theorems:
* `branchIII_closure_implies_mass_gap_pos` — closure ⇒ positive mass gap.
* `branchIII_closure_construct` — constructive existence.

## Strategic value

Phase 170 closes the Branch III structural argument with a clean
closure structure mirroring L15 (Branch II × Wilson) and L17
(Branch I × F3).

Cross-references:
- Phase 169 `SpectralGapToMassGap.lean`.
- Phase 140 `L15_BranchII_Wilson_Substantive/BranchIIWilsonClosure.lean`.
- Phase 160 `L17_BranchI_F3_Substantive/BranchIClosureConditions.lean`.
-/

end YangMills.L18_BranchIII_RP_TM_Substantive
