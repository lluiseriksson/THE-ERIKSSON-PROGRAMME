# Draft for Mathlib PR: Finite Product Haar Measure

**Status:** DRAFT (Node L0.7 blocked, Mathlib Blocked M01)
**Target:** Mathlib4

**Objective**: We need exact support for finite products of Haar measures over compact Lie groups (e.g. `SU(N)` on edges of a lattice box).

## The Gap (M01)
Mathlib has Haar measure and product measures, but constructing a product measure over a `Fintype` index set `E` (the edges) where each factor is a normalized Haar measure on a compact group $G$ requires a seamless `MeasureSpace (E → G)` that inherits left/right invariance correctly and maintains proper normalization.

## Specification
```lean
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod

variables {E : Type*} [Fintype E] {G : Type*} [TopologicalSpace G] [TopologicalGroup G] [MeasureSpace G]

-- Target theorem we need in Mathlib:
-- The product measure on (E → G) is the unique left-invariant probability measure
-- (assuming G is compact and normalized to probability 1).
```

## Action Plan
1. Check current state of `Mathlib.MeasureTheory.Measure.Pi`.
2. Determine if `volume` on `E → G` is automatically Haar when `volume` on `G` is Haar.
3. Verify that the measure remains properly normalized and positive.
4. If it requires manual instances, write them cleanly and prepare PR.
