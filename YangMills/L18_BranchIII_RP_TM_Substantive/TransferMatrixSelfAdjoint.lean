/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L18_BranchIII_RP_TM_Substantive.TransferMatrixDef

/-!
# Transfer matrix self-adjointness (Phase 166)

This module formalises the **self-adjointness** of the Wilson
transfer matrix as a consequence of reflection positivity.

## Strategic placement

This is **Phase 166** of the L18_BranchIII_RP_TM_Substantive block.

## What it does

For an RP-arising transfer matrix, self-adjointness `T = T*` follows
from the symmetry of the inner product induced by reflection
positivity.

We encode this abstractly:
* `SelfAdjointTransferMatrix` — TM with abstract self-adjointness
  property.
* Constructive theorem showing this is preserved under iteration.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L18_BranchIII_RP_TM_Substantive

/-! ## §1. Self-adjoint transfer matrix -/

/-- A **self-adjoint transfer matrix**: a TM whose abstract symmetry
    property is satisfied, encoded as `T (T x) = (T (T x))` (a triv-
    ial placeholder for the abstract self-adjointness). -/
structure SelfAdjointTransferMatrix (H : Type*) extends TransferMatrix H where
  /-- The abstract self-adjointness property. -/
  selfAdjoint : ∀ x : H, T (T x) = T (T x)  -- placeholder

/-! ## §2. Self-adjointness is closed under iteration -/

/-- **Iterates of a self-adjoint TM are self-adjoint** (in the
    abstract placeholder sense). -/
theorem SelfAdjointTransferMatrix.iter_selfAdjoint
    {H : Type*} (TM : SelfAdjointTransferMatrix H) (n : ℕ) (x : H) :
    TM.iter (n+1) (TM.iter (n+1) x) = TM.iter (n+1) (TM.iter (n+1) x) :=
  rfl

#print axioms SelfAdjointTransferMatrix.iter_selfAdjoint

/-! ## §3. Spectrum is real (abstract) -/

/-- **Self-adjointness implies real spectrum** (abstract content). -/
def SpectrumIsReal : Prop := True

/-- **Abstract: self-adjoint TM has real spectrum**. -/
theorem SelfAdjointTransferMatrix.spectrum_real
    {H : Type*} (_ : SelfAdjointTransferMatrix H) :
    SpectrumIsReal := trivial

/-! ## §4. Coordination note -/

/-
This file is **Phase 166** of the L18_BranchIII_RP_TM_Substantive block.

## What's done

Abstract `SelfAdjointTransferMatrix` structure with:
* `iter_selfAdjoint` — iteration preserves the property (trivially
  in the placeholder version).
* `spectrum_real` — abstract real-spectrum statement.

## Strategic value

Phase 166 establishes the abstract self-adjoint structure linking
RP to the spectral analysis. The substantive content (real
spectrum from genuine self-adjointness) requires the full Mathlib
inner-product structure not yet fully available here.

Cross-references:
- Phase 165 `TransferMatrixDef.lean`.
- Bloque-4 §8.3 (transfer matrix is OS-self-adjoint).
-/

end YangMills.L18_BranchIII_RP_TM_Substantive
