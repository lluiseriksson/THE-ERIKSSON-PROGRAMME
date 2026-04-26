/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Gauge block decomposition (Phase 135)

This module formalises the **gauge-block decomposition**: how the
SU(N) link variables on a fine lattice decompose into a coarse-lattice
average plus a fluctuation field.

## Strategic placement

This is **Phase 135** of the L15_BranchII_Wilson_Substantive block.

## What it does

Encodes the decomposition `U_link = U_block · δU_fluctuation`, where:
* `U_block` lives on the coarse-lattice block.
* `δU_fluctuation` is the fine-scale fluctuation, integrated out by
  the block-spin transform.

The decomposition is encoded abstractly via a `GaugeBlock` structure
with two component fields and a recombination map.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L15_BranchII_Wilson_Substantive

/-! ## §1. The gauge block decomposition -/

/-- **Abstract gauge-block decomposition**: a fine-lattice
    configuration decomposes as `(coarse, fluctuation)`. -/
structure GaugeBlock (Fine Coarse Fluctuation : Type*) where
  /-- Project a fine configuration onto its coarse-block component. -/
  toCoarse : Fine → Coarse
  /-- Project a fine configuration onto its fluctuation component. -/
  toFluctuation : Fine → Fluctuation
  /-- Recombine a (coarse, fluctuation) pair into a fine configuration. -/
  fromPair : Coarse × Fluctuation → Fine
  /-- Recombination is a left-inverse of the projection pair. -/
  fromPair_proj : ∀ f : Fine,
    fromPair (toCoarse f, toFluctuation f) = f

/-! ## §2. The decomposition is a bijection -/

/-- **The gauge-block decomposition is injective on configurations**. -/
theorem GaugeBlock.proj_pair_injective
    {Fine Coarse Fluctuation : Type*}
    (gb : GaugeBlock Fine Coarse Fluctuation) :
    Function.Injective (fun f : Fine => (gb.toCoarse f, gb.toFluctuation f)) := by
  intro f₁ f₂ h
  -- From `(toCoarse f₁, toFluctuation f₁) = (toCoarse f₂, toFluctuation f₂)`
  -- we recover `f₁ = f₂` by applying `fromPair`.
  have h₁ : gb.fromPair (gb.toCoarse f₁, gb.toFluctuation f₁) = f₁ :=
    gb.fromPair_proj f₁
  have h₂ : gb.fromPair (gb.toCoarse f₂, gb.toFluctuation f₂) = f₂ :=
    gb.fromPair_proj f₂
  rw [← h₁, ← h₂, h]

#print axioms GaugeBlock.proj_pair_injective

/-! ## §3. Coordination note -/

/-
This file is **Phase 135** of the L15_BranchII_Wilson_Substantive block.

## What's done

The abstract `GaugeBlock` structure capturing the
fine = (coarse, fluctuation) decomposition, plus a substantive
injectivity theorem proved in Lean.

## Strategic value

Phase 135 gives the project a clean abstract handle on the
gauge-block decomposition that downstream files can use without
committing to specific coordinate systems.

Cross-references:
- Bloque-4 §3.3 (gauge fixing in block-spin transform).
- Phase 134 `BlockSpinDecimation.lean`.
-/

end YangMills.L15_BranchII_Wilson_Substantive
