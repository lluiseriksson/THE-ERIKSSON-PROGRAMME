/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib

/-!
# Lattice Schwinger Functions (Bloque-4 §2.3 / Definition 2.3)

This module formalises the **lattice Schwinger functions** — the
n-point correlation functions of the Wilson Gibbs measure, viewed as
distributions on `ℝ^{4n}`.

## Strategic placement

This is **Phase 103** of the L8_LatticeToContinuum block (Phases
103-107), the bridge between L7_Multiscale (lattice mass gap) and
L9_OSReconstruction (continuum OS state).

## Definition (Bloque-4 §2.3)

For a lattice spacing `η`, physical volume `L_phys`, lattice
`Λ_η = (ηℤ/L_phys ℤ)^4`, and gauge-invariant local observables
`O_1, ..., O_n`, the Schwinger function is:

  `S_n^η(x_1, ..., x_n) := E_{µ_η}[O_1(x_1) · ... · O_n(x_n)]`

extended to `ℝ^{4n}` via the projection `π_η : ℝ → Λ_η`.

The continuum Schwinger functions (Bloque-4 Theorem 1.4(a)) are
subsequential limits of these as `η → 0` and `L_phys → ∞`.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.L8_LatticeToContinuum

open MeasureTheory

/-! ## §1. Lattice projection and observables -/

/-- The **lattice projection** `π_η : ℝ → ηℤ` rounds a real number
    to the nearest lattice site. -/
noncomputable def latticeProjection (η : ℝ) (hη : 0 < η) (y : ℝ) : ℝ :=
  η * ⌊y / η⌋

/-- Periodic restriction to the torus `[-L/2, L/2)`. -/
noncomputable def torusReduction (L : ℝ) (hL : 0 < L) (y : ℝ) : ℝ :=
  y - L * ⌊(y + L/2) / L⌋

/-! ## §2. Lattice Schwinger functions (abstract) -/

/-- An **abstract lattice Schwinger function bundle**: bundles the
    lattice spacing, physical volume, and the n-point function. -/
structure LatticeSchwingerFunctionBundle
    (n : ℕ) where
  /-- Lattice spacing. -/
  η : ℝ
  hη_pos : 0 < η
  /-- Physical volume. -/
  L_phys : ℝ
  hL_pos : 0 < L_phys
  /-- The n-point Schwinger function: `S_n^η : (ℝ^4)^n → ℝ`. -/
  S_n : (Fin n → Fin 4 → ℝ) → ℝ
  /-- Boundedness: |S_n^η| ≤ 1. -/
  bound : ∀ y : Fin n → Fin 4 → ℝ, |S_n y| ≤ 1
  /-- Lattice translation invariance: `S_n^η(x + ηℓ) = S_n^η(x)` for
      all lattice translations `ℓ ∈ Λ_η`. -/
  translation_invariance : ∀ (y : Fin n → Fin 4 → ℝ) (ℓ : Fin 4 → ℤ),
    S_n (fun i j => y i j + η * (ℓ j : ℝ)) = S_n y
  /-- W4 (hypercubic) covariance: `S_n^η(σ x) = S_n^η(x)` for `σ ∈ W_4`.
      Hypercubic group elements are signed permutations of coordinates. -/
  W4_covariance : ∀ (y : Fin n → Fin 4 → ℝ)
    (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → Bool),
    S_n (fun i j => (if s (σ j) then 1 else -1) * y i (σ j)) = S_n y

/-! ## §3. As a tempered distribution -/

/-- The lattice Schwinger function as a function in `L^∞(ℝ^{4n})`,
    extended periodically. -/
noncomputable def asLInfinity {n : ℕ}
    (S : LatticeSchwingerFunctionBundle n)
    (y : Fin n → Fin 4 → ℝ) : ℝ :=
  -- Apply the lattice projection per coordinate first.
  S.S_n (fun i j => latticeProjection S.η S.hη_pos
    (torusReduction S.L_phys S.hL_pos (y i j)))

/-- The lattice Schwinger function pairs with Schwartz test
    functions to give a tempered distribution. -/
def pairWithTestFunction
    {n : ℕ} (S : LatticeSchwingerFunctionBundle n)
    (f : (Fin n → Fin 4 → ℝ) → ℝ) (_hf_integrable : True) : Prop :=
  -- Standard pairing ⟨S_n^η, f⟩ := ∫ S_n^η(y) f(y) dy.
  -- For Schwartz test functions, this is well-defined since
  -- S_n^η is bounded.
  True

/-! ## §4. Coordination note -/

/-
This file is **Phase 103** of the L8_LatticeToContinuum block.

## Status

* `latticeProjection` and `torusReduction` definitions.
* `LatticeSchwingerFunctionBundle` data structure.
* `asLInfinity` extension.
* `pairWithTestFunction` predicate.

## What's done

The structural skeleton for lattice Schwinger functions following
Bloque-4 Definition 2.3. Captures the bound `|S_n| ≤ 1`,
translation invariance, and W4 covariance.

## What's NOT done

* The concrete connection to the Wilson Gibbs measure (would require
  importing `L1_GibbsMeasure/`).
* The detailed Schwartz pairing (`pairWithTestFunction` is a
  placeholder).

## Strategic value

Phase 103 provides the **lattice-side data** that Phase 104 (OS0
temperedness), Phase 105 (subsequential continuum limit), Phase 106
(boundary insensitivity), and Phase 107 (full bridge) all build on.

Cross-references:
- Phase 84: `BLUEPRINT_MultiscaleDecoupling.md`.
- Phase 97: `L7_Multiscale/MultiscaleDecouplingPackage.lean`.
- Bloque-4 §2.3 Definition 2.3.
-/

end YangMills.L8_LatticeToContinuum
