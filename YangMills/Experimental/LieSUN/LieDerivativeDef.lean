import Mathlib

/-!
# Experimental: Abstract Lie Derivative via Curves

This file proves linearity and constancy of directional derivatives
defined via curves, without any dependence on SU(N) or Lie group structure.

**Goal:** Validate that `deriv_add`, `deriv_const_mul`, `deriv_const` from
Mathlib are sufficient to prove the three properties currently axiomatized
in `SUN_DirichletForm.lean`.

**Status:** Sandbox — does NOT import from P8_PhysicalGap.

Layer A (this file): Fully abstract, no SU(N) required.
Layer B (future):    Concrete exponential curves on SU(N).
Layer C (future):    Identification with opaque lieDerivative.
-/

namespace YangMills.Experimental.LieSUN

open Filter

variable {G : Type*} [TopologicalSpace G]

/-! ## Definition -/

/-- The directional derivative of f : G → ℝ along a curve through U.
    `curve U t` is the position at time t, with `curve U 0 = U` (not enforced here).
    Concretely: lieDerivativeVia curve f U = d/dt f(curve U t) |_{t=0}. -/
noncomputable def lieDerivativeVia
    (curve : G → ℝ → G)
    (f : G → ℝ) (U : G) : ℝ :=
  deriv (fun t => f (curve U t)) 0

/-! ## Layer A: Linearity theorems from Mathlib's deriv API -/

/-- THEOREM (from deriv_add):
    The Lie derivative of f + g equals the sum of Lie derivatives.
    Note: DifferentiableAt hypotheses are required — deriv is junk (= 0)
    for non-differentiable functions. -/
theorem lieDerivativeVia_add
    (curve : G → ℝ → G) (f g : G → ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (curve U t)) 0) :
    lieDerivativeVia curve (f + g) U =
    lieDerivativeVia curve f U + lieDerivativeVia curve g U := by
  simp only [lieDerivativeVia, Pi.add_apply]
  exact deriv_add hf hg

/-- THEOREM (from deriv_const_mul):
    The Lie derivative of c * f equals c * Lie derivative of f. -/
theorem lieDerivativeVia_smul
    (curve : G → ℝ → G) (f : G → ℝ) (c : ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0) :
    lieDerivativeVia curve (fun x => c * f x) U =
    c * lieDerivativeVia curve f U := by
  simp only [lieDerivativeVia]
  have : deriv (fun t => c * f (curve U t)) 0 = c * deriv (fun t => f (curve U t)) 0 :=
    deriv_const_mul c hf
  convert this using 2
  ext t; ring

/-- THEOREM (from deriv_const — UNCONDITIONAL):
    The Lie derivative of a constant function is always zero.
    No DifferentiableAt hypothesis needed! -/
theorem lieDerivativeVia_const
    (curve : G → ℝ → G) (c : ℝ) (U : G) :
    lieDerivativeVia curve (fun _ => c) U = 0 := by
  simp [lieDerivativeVia, deriv_const]

/-- THEOREM: Lie derivative kills constant shifts: D(f + c) = D(f).
    Derived from add + const above. -/
theorem lieDerivativeVia_const_add
    (curve : G → ℝ → G) (f : G → ℝ) (c : ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0) :
    lieDerivativeVia curve (fun x => f x + c) U =
    lieDerivativeVia curve f U := by
  have h : lieDerivativeVia curve (fun x => f x + c) U =
           lieDerivativeVia curve f U +
           lieDerivativeVia curve (fun _ => c) U := by
    have hc : DifferentiableAt ℝ (fun t => (fun _ => c) (curve U t)) 0 :=
      differentiableAt_const c
    convert lieDerivativeVia_add curve f (fun _ => c) U hf hc using 2
    ext x; simp
  rw [h, lieDerivativeVia_const, add_zero]

/-! ## Summary: what compiles clean -/

-- All 4 theorems above compile without sorry.
-- The key insight: `deriv_const` is unconditional (DifferentiableAt not needed).
-- `deriv_add` and `deriv_const_mul` require DifferentiableAt.
-- This matches exactly the axiom structure in P8_PhysicalGap/SUN_DirichletForm.lean.

end YangMills.Experimental.LieSUN
