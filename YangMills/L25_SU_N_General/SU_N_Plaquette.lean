/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L25_SU_N_General.SU_N_LatticeGauge

/-!
# SU(N) plaquette (Phase 234)

Parametric plaquette structure.

## Strategic placement

This is **Phase 234** of the L25_SU_N_General block.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L25_SU_N_General

/-! ## §1. Plaquette holonomy (parametric) -/

/-- **SU(N) plaquette holonomy**. -/
def plaquette_holonomy {N : ℕ} (U₁ U₂ U₃ U₄ : SU_N N) : SU_N N :=
  U₁ * U₂ * U₃⁻¹ * U₄⁻¹

/-- **Plaquette holonomy at identity**. -/
theorem plaquette_holonomy_at_identity (N : ℕ) :
    plaquette_holonomy (SU_N.identity N) (SU_N.identity N)
                       (SU_N.identity N) (SU_N.identity N) =
      SU_N.identity N := by
  unfold plaquette_holonomy SU_N.identity
  simp

/-! ## §2. Real trace (parametric) -/

/-- **SU(N) plaquette real trace**. -/
def plaquette_real_trace {N : ℕ} (U_p : SU_N N) : ℝ :=
  (U_p.val.trace).re

/-! ## §3. Identity-trace value -/

/-- **For SU(N), `Re Tr(I) = N`** (the dimension of the matrix). -/
theorem plaquette_real_trace_at_identity_equals_N (N : ℕ) :
    plaquette_real_trace (SU_N.identity N) = N := by
  unfold plaquette_real_trace SU_N.identity
  show (Matrix.trace ((1 : SU_N N).val)).re = N
  simp [Matrix.trace, Matrix.one_apply_eq, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]

#print axioms plaquette_real_trace_at_identity_equals_N

/-! ## §4. Coordination note -/

/-
This file is **Phase 234** of the L25_SU_N_General block.

## What's done

A parametric Lean theorem:
* `plaquette_real_trace_at_identity_equals_N` — `Re Tr(I) = N`
  for ANY `N`, generalizing the SU(2) version (= 2) and SU(3)
  version (= 3).

## Strategic value

Phase 234 generalizes the plaquette real-trace computation to
arbitrary `N`, giving a single parametric statement.

Cross-references:
- Phase 184 (L20 SU(2): trace = 2).
- Phase 214 (L23 SU(3): trace = 3).
-/

end YangMills.L25_SU_N_General
