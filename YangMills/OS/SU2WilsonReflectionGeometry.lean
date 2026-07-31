/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/

import YangMills.OS.SU2WilsonReflectionKernel

/-!
# A finite SU(2) reflection cut

This file contains only the geometry and the exact splitting identity.  Kernel
positivity remains in `SU2WilsonReflectionKernel`; the endpoint combines them
in `SU2WilsonReflectionEndpoint`.

The configuration shape is explicitly `Half × Cross × Half`.  This avoids the
fixed-edge obstruction of a bare `Half × Half` swap.  Reflection exchanges the
two halves and inverts every oriented crossing link.
-/

noncomputable section

open Complex MeasureTheory

namespace YangMills.OS

/-- Configurations adapted to a reflection cut. -/
abbrev SU2CutConfig (Half Cross : Type*) :=
  (Half → SU2) × (Cross → SU2) × (Half → SU2)

/-- Physical link reflection: swap the half-configurations and reverse the
orientation of crossing links by group inversion. -/
def reflectSU2Cut {Half Cross : Type*} :
    SU2CutConfig Half Cross → SU2CutConfig Half Cross :=
  fun cfg => (cfg.2.2, fun e => (cfg.2.1 e)⁻¹, cfg.1)

theorem reflectSU2Cut_involutive {Half Cross : Type*} :
    Function.Involutive
      (reflectSU2Cut : SU2CutConfig Half Cross → SU2CutConfig Half Cross) := by
  intro cfg
  ext <;> simp [reflectSU2Cut]

/-- The declared minimal finite cut: one boundary variable in each half and
one oriented crossing link. -/
abbrev SU2OnePlaquetteCut := SU2CutConfig Unit Unit

def mkSU2OnePlaquetteCut (x c y : SU2) : SU2OnePlaquetteCut :=
  (fun _ => x, fun _ => c, fun _ => y)

def onePlaquetteLeft (cfg : SU2OnePlaquetteCut) : SU2 :=
  cfg.1 ()

def onePlaquetteCross (cfg : SU2OnePlaquetteCut) : SU2 :=
  cfg.2.1 ()

def onePlaquetteRight (cfg : SU2OnePlaquetteCut) : SU2 :=
  cfg.2.2 ()

@[simp] theorem onePlaquetteLeft_mk (x c y : SU2) :
    onePlaquetteLeft (mkSU2OnePlaquetteCut x c y) = x := rfl

@[simp] theorem onePlaquetteCross_mk (x c y : SU2) :
    onePlaquetteCross (mkSU2OnePlaquetteCut x c y) = c := rfl

@[simp] theorem onePlaquetteRight_mk (x c y : SU2) :
    onePlaquetteRight (mkSU2OnePlaquetteCut x c y) = y := rfl

def onePlaquetteDressedLeft (cfg : SU2OnePlaquetteCut) : SU2 :=
  onePlaquetteLeft cfg * onePlaquetteCross cfg

def onePlaquetteDressedRight (cfg : SU2OnePlaquetteCut) : SU2 :=
  onePlaquetteRight cfg * onePlaquetteCross cfg

@[simp] theorem onePlaquetteLeft_reflect (cfg : SU2OnePlaquetteCut) :
    onePlaquetteLeft (reflectSU2Cut cfg) = onePlaquetteRight cfg := rfl

@[simp] theorem onePlaquetteRight_reflect (cfg : SU2OnePlaquetteCut) :
    onePlaquetteRight (reflectSU2Cut cfg) = onePlaquetteLeft cfg := rfl

@[simp] theorem onePlaquetteCross_reflect (cfg : SU2OnePlaquetteCut) :
    onePlaquetteCross (reflectSU2Cut cfg) = (onePlaquetteCross cfg)⁻¹ := rfl

set_option maxHeartbeats 10000 in
/-- The crossing link transports both boundary holonomies to the same frame
and therefore cancels from their relative Wilson holonomy. -/
theorem su2WilsonCrossingKernel_dressed (β : ℝ)
    (cfg : SU2OnePlaquetteCut) :
    su2WilsonCrossingKernel β
        (onePlaquetteDressedLeft cfg) (onePlaquetteDressedRight cfg) =
      su2WilsonCrossingKernel β
        (onePlaquetteLeft cfg) (onePlaquetteRight cfg) := by
  have hcancel :
      onePlaquetteDressedLeft cfg * (onePlaquetteDressedRight cfg)⁻¹ =
        onePlaquetteLeft cfg * (onePlaquetteRight cfg)⁻¹ := by
    unfold onePlaquetteDressedLeft onePlaquetteDressedRight
    group
  exact congrArg
    (fun z : SU2 =>
      ((Real.exp ((β / 2) *
        (Matrix.trace
          ((z : SU2) : Matrix (Fin 2) (Fin 2) ℂ)).re) : ℝ) : ℂ))
    hcancel

/-- Exact finite-cut Wilson weight.  `leftWeight` and `rightWeight` collect
plaquettes wholly contained in the two halves; the middle factor is the single
physical crossing plaquette, written in the common frame selected by the
crossing link. -/
def su2OnePlaquetteCutWeight (β : ℝ)
    (leftWeight rightWeight : SU2 → ℂ) (cfg : SU2OnePlaquetteCut) : ℂ :=
  leftWeight (onePlaquetteLeft cfg) *
    su2WilsonCrossingKernel β
      (onePlaquetteDressedLeft cfg) (onePlaquetteDressedRight cfg) *
    rightWeight (onePlaquetteRight cfg)

/-- Gate (4): the concrete finite geometry splits into left, crossing, and
right factors with the exact Wilson crossing kernel. -/
theorem su2OnePlaquetteCutWeight_splitting (β : ℝ)
    (leftWeight rightWeight : SU2 → ℂ) (cfg : SU2OnePlaquetteCut) :
    su2OnePlaquetteCutWeight β leftWeight rightWeight cfg =
      leftWeight (onePlaquetteLeft cfg) *
        su2WilsonCrossingKernel β
          (onePlaquetteLeft cfg) (onePlaquetteRight cfg) *
        rightWeight (onePlaquetteRight cfg) := by
  rw [su2OnePlaquetteCutWeight, su2WilsonCrossingKernel_dressed]

/-- The exact Wilson weight of the minimal cut.  There are no plaquettes
strictly inside either half, so both internal half weights are one. -/
def su2OnePlaquetteWilsonWeight (β : ℝ)
    (cfg : SU2OnePlaquetteCut) : ℂ :=
  su2OnePlaquetteCutWeight β (fun _ => 1) (fun _ => 1) cfg

theorem su2OnePlaquetteWilsonWeight_eq_kernel (β : ℝ)
    (cfg : SU2OnePlaquetteCut) :
    su2OnePlaquetteWilsonWeight β cfg =
      su2WilsonCrossingKernel β
        (onePlaquetteLeft cfg) (onePlaquetteRight cfg) := by
  simp [su2OnePlaquetteWilsonWeight,
    su2OnePlaquetteCutWeight_splitting]

/-- A half-observable is read on the right half.  Reflection moves it to the
left half and complex conjugation supplies the OS antilinearity. -/
def su2OnePlaquetteHalfObservable (F : SU2 → ℂ)
    (cfg : SU2OnePlaquetteCut) : ℂ :=
  F (onePlaquetteRight cfg)

/-- Pointwise OS integrand before integrating the finite cut variables. -/
def su2OnePlaquetteReflectedIntegrand
    (β : ℝ) (F : SU2 → ℂ) (x c y : SU2) : ℂ :=
  let cfg := mkSU2OnePlaquetteCut x c y
  star (su2OnePlaquetteHalfObservable F (reflectSU2Cut cfg)) *
    su2OnePlaquetteWilsonWeight β cfg *
    su2OnePlaquetteHalfObservable F cfg

theorem su2OnePlaquetteReflectedIntegrand_eq
    (β : ℝ) (F : SU2 → ℂ) (x c y : SU2) :
    su2OnePlaquetteReflectedIntegrand β F x c y =
      star (F x) * su2WilsonCrossingKernel β x y * F y := by
  rw [su2OnePlaquetteReflectedIntegrand,
    su2OnePlaquetteHalfObservable,
    su2OnePlaquetteWilsonWeight_eq_kernel]
  rfl

/-- The full reflected pairing on the minimal cut.  All three SU(2)
variables, including the gauge-redundant crossing transporter, are integrated
against normalized Haar measure. -/
def su2OnePlaquetteReflectedPairing (β : ℝ) (F : SU2 → ℂ) : ℂ :=
  let μ := sunHaarProb 2
  ∫ x, ∫ y, ∫ c,
    su2OnePlaquetteReflectedIntegrand β F x c y ∂μ ∂μ ∂μ

set_option maxHeartbeats 10000 in
/-- The geometry/splitting bridge: the full reflected cut pairing is exactly
the analytic crossing-kernel quadratic form.  The middle Haar integral is one
because the common crossing transporter cancels from the relative holonomy. -/
theorem su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm
    (β : ℝ) (F : SU2 → ℂ) :
    su2OnePlaquetteReflectedPairing β F =
      kernelIntegralForm (sunHaarProb 2)
        (su2WilsonCrossingKernel β) F := by
  unfold su2OnePlaquetteReflectedPairing kernelIntegralForm
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  rw [integral_congr_ae
    (Filter.Eventually.of_forall
      (fun c => su2OnePlaquetteReflectedIntegrand_eq β F x c y))]
  simp

end YangMills.OS
