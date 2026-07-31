/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/

import YangMills.OS.SU2WilsonReflectionKernel

/-!
**Scope limitation — read before the title.**  The `Cross` variable is a
gauge-pure auxiliary transporter.  It does not participate in the effective
weight or pairing after cancellation, and its inversion by `reflectSU2Cut` is
not exercised by the positivity result.  This geometric limitation does not
weaken the separately proved complex Haar positivity for every continuous
observable or the sharp trace bound `β/4`.

# An auxiliary SU(2) reflection cut

This file defines the auxiliary cut and proves exact cancellation identities.
It does not derive a lattice plaquette Wilson weight or a physical
factorization theorem.  Kernel positivity remains in
`SU2WilsonReflectionKernel`; `SU2WilsonReflectionEndpoint` transports it to
the declared auxiliary pairing.

The configuration shape is `Half × Cross × Half`.  Reflection exchanges the
two halves and inverts every oriented crossing link at the type level, but the
effective weight and pairing below are independent of `Cross`.
-/

noncomputable section

open Complex MeasureTheory

namespace YangMills.OS

/-- Configurations adapted to a reflection cut. -/
abbrev SU2CutConfig (Half Cross : Type*) :=
  (Half → SU2) × (Cross → SU2) × (Half → SU2)

/-- Auxiliary typed reflection: swap the half-configurations and reverse the
orientation of crossing links by group inversion.  The effective result below
does not depend on the crossing links. -/
def reflectSU2Cut {Half Cross : Type*} :
    SU2CutConfig Half Cross → SU2CutConfig Half Cross :=
  fun cfg => (cfg.2.2, fun e => (cfg.2.1 e)⁻¹, cfg.1)

theorem reflectSU2Cut_involutive {Half Cross : Type*} :
    Function.Involutive
      (reflectSU2Cut : SU2CutConfig Half Cross → SU2CutConfig Half Cross) := by
  intro cfg
  ext <;> simp [reflectSU2Cut]

/-- The declared minimal auxiliary cut: one boundary variable in each half
and one gauge-pure crossing transporter. -/
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

/-- A declared factorized auxiliary weight.  `leftWeight` and `rightWeight`
are arbitrary factors, and the middle factor is the dressed kernel.  This is
a definition in product form, not a derivation from a lattice plaquette
Wilson weight. -/
def su2OnePlaquetteCutWeight (β : ℝ)
    (leftWeight rightWeight : SU2 → ℂ) (cfg : SU2OnePlaquetteCut) : ℂ :=
  leftWeight (onePlaquetteLeft cfg) *
    su2WilsonCrossingKernel β
      (onePlaquetteDressedLeft cfg) (onePlaquetteDressedRight cfg) *
    rightWeight (onePlaquetteRight cfg)

/-- Exact cancellation equality: in the already factorized auxiliary weight,
the common gauge-pure transporter can be removed from the dressed kernel.
This does not derive a physical plaquette factorization. -/
theorem su2OnePlaquetteCutWeight_eq_undressedKernel (β : ℝ)
    (leftWeight rightWeight : SU2 → ℂ) (cfg : SU2OnePlaquetteCut) :
    su2OnePlaquetteCutWeight β leftWeight rightWeight cfg =
      leftWeight (onePlaquetteLeft cfg) *
        su2WilsonCrossingKernel β
          (onePlaquetteLeft cfg) (onePlaquetteRight cfg) *
        rightWeight (onePlaquetteRight cfg) := by
  rw [su2OnePlaquetteCutWeight, su2WilsonCrossingKernel_dressed]

/-- The unit-half specialization of the declared auxiliary weight.  This
specialization is not derived from the repository's lattice Wilson action. -/
def su2OnePlaquetteWilsonWeight (β : ℝ)
    (cfg : SU2OnePlaquetteCut) : ℂ :=
  su2OnePlaquetteCutWeight β (fun _ => 1) (fun _ => 1) cfg

theorem su2OnePlaquetteWilsonWeight_eq_kernel (β : ℝ)
    (cfg : SU2OnePlaquetteCut) :
    su2OnePlaquetteWilsonWeight β cfg =
      su2WilsonCrossingKernel β
        (onePlaquetteLeft cfg) (onePlaquetteRight cfg) := by
  simp [su2OnePlaquetteWilsonWeight,
    su2OnePlaquetteCutWeight_eq_undressedKernel]

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
/-- The auxiliary-pairing bridge: the declared reflected pairing is exactly
the analytic kernel quadratic form.  The middle Haar integral is one because
the common gauge-pure transporter cancels, so its inversion under reflection
does not contribute to this equality or to the resulting positivity theorem. -/
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
