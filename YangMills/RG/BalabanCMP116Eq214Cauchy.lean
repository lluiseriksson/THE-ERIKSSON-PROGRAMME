/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Fin.Tuple.Basic

/-!
# CMP116 equation (2.14): finite families of squared Cauchy kernels

Each interpolation coordinate in Balaban CMP116 equation (2.14) contributes

`∫₀¹ ds (2πi)⁻¹ ∮ dσ (σ - s)⁻² f(σ)`.

Mathlib's `Complex.cderiv` is definitionally this normalized squared Cauchy
kernel.  The definitions below therefore represent the source expression
literally, without introducing a second contour normalization.  The recursive
finite-family operator keeps the later coordinates inside the function passed
to the earlier Cauchy derivative; consequently it preserves arbitrary
cross-coordinate dependence in the Gaussian and interaction factors of
equation (2.14).

Honest scope: this file constructs the exact contour/interpolation operator.
It does not yet prove analyticity of the physical CMP116 integrand, independence
of an enumeration of a finite carrier, or the norm estimate used in (2.26).
-/

namespace YangMills.RG

open Set Metric MeasureTheory Complex intervalIntegral
open scoped Real Topology

/-- One interpolation/Cauchy step in CMP116 equation (2.14). -/
noncomputable def cmp116Eq214CauchyStep
    (radius : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ s : ℝ in (0 : ℝ)..1, Complex.cderiv radius f (s : ℂ)

/-- The one-coordinate operator is literally the normalized squared Cauchy
kernel printed in CMP116 equation (2.14). -/
theorem cmp116Eq214CauchyStep_eq_squaredKernel
    (radius : ℝ) (f : ℂ → ℂ) :
    cmp116Eq214CauchyStep radius f =
      ∫ s : ℝ in (0 : ℝ)..1,
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ w in C((s : ℂ), radius),
            ((w - (s : ℂ)) ^ 2)⁻¹ • f w := by
  rfl

/-- Iterated source-ordered Cauchy interpolation over `n` coordinates.

The order is explicit: coordinate `0` is integrated first and the remaining
coordinates retain their dependence on its complex contour variable. -/
noncomputable def cmp116Eq214CauchyFamily :
    (n : ℕ) → (Fin n → ℝ) → ((Fin n → ℂ) → ℂ) → ℂ
  | 0, _, F => F Fin.elim0
  | n + 1, radius, F =>
      cmp116Eq214CauchyStep (radius 0) fun z =>
        cmp116Eq214CauchyFamily n (fun i => radius i.succ) fun tail =>
          F (Fin.cons z tail)

@[simp] theorem cmp116Eq214CauchyFamily_zero
    (radius : Fin 0 → ℝ) (F : (Fin 0 → ℂ) → ℂ) :
    cmp116Eq214CauchyFamily 0 radius F = F Fin.elim0 := by
  rfl

/-- The recursive equation used twice in (2.14): once for the `σ(Δ)` family
and once for the `τ(Y)` family. -/
theorem cmp116Eq214CauchyFamily_succ
    (n : ℕ) (radius : Fin (n + 1) → ℝ)
    (F : (Fin (n + 1) → ℂ) → ℂ) :
    cmp116Eq214CauchyFamily (n + 1) radius F =
      cmp116Eq214CauchyStep (radius 0) (fun z =>
        cmp116Eq214CauchyFamily n (fun i => radius i.succ) (fun tail =>
          F (Fin.cons z tail))) := by
  rfl

/-- On an analytic disk, the source kernel is the ordinary complex
derivative.  This is the direct bridge used later to bound each contour step. -/
theorem cmp116Eq214CauchyKernel_eq_deriv
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ} {radius : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < radius) (hzr : closedBall z radius ⊆ U) :
    Complex.cderiv radius f z = deriv f z :=
  Complex.cderiv_eq_deriv hU hf hr hzr

end YangMills.RG
