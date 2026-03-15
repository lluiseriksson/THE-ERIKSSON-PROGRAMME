import Mathlib

/-!
# Experimental: Abstract Lie Derivative via Curves

Defines `lieDerivativeVia` and proves linearity/constancy from Mathlib.
Zero axioms, zero sorrys. SANDBOX — not imported by main project.

Key insight:
- `deriv_const` is UNCONDITIONAL (no DifferentiableAt needed)
- `deriv_add`, `deriv_const_mul` require DifferentiableAt hypotheses
-/

universe u

variable {G : Type u}

/-! ## Definition -/

/-- Directional derivative of f along a curve: d/dt f(curve U t) |_{t=0}. -/
noncomputable def lieDerivativeVia
    (curve : G → ℝ → G)
    (f : G → ℝ) (U : G) : ℝ :=
  deriv (fun t => f (curve U t)) 0

/-! ## Theorems -/

theorem lieDerivativeVia_add
    (curve : G → ℝ → G) (f g : G → ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (curve U t)) 0) :
    lieDerivativeVia curve (fun x => f x + g x) U =
      lieDerivativeVia curve f U + lieDerivativeVia curve g U := by
  unfold lieDerivativeVia
  exact deriv_add hf hg

theorem lieDerivativeVia_smul
    (curve : G → ℝ → G) (f : G → ℝ) (c : ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0) :
    lieDerivativeVia curve (fun x => c * f x) U =
      c * lieDerivativeVia curve f U := by
  unfold lieDerivativeVia
  exact deriv_const_mul c hf

theorem lieDerivativeVia_const
    (curve : G → ℝ → G) (c : ℝ) (U : G) :
    lieDerivativeVia curve (fun _ => c) U = 0 := by
  unfold lieDerivativeVia
  exact deriv_const 0 c

theorem lieDerivativeVia_const_add
    (curve : G → ℝ → G) (f : G → ℝ) (c : ℝ) (U : G)
    (hf : DifferentiableAt ℝ (fun t => f (curve U t)) 0) :
    lieDerivativeVia curve (fun x => f x + c) U =
      lieDerivativeVia curve f U := by
  have h : lieDerivativeVia curve (fun x => f x + c) U =
           lieDerivativeVia curve f U +
           lieDerivativeVia curve (fun _ => c) U := by
    unfold lieDerivativeVia
    exact deriv_add hf (differentiableAt_const c)
  rw [h, lieDerivativeVia_const, add_zero]
