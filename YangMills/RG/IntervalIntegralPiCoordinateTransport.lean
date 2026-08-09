/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Integral.Pi
import YangMills.RG.IntervalIntegralSliceTransport

/-!
# PRE-VALIDATION: coordinate transport through a finite product integral

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

This module isolates the measure-theoretic step needed to iterate a physical
one-coordinate contour equality.  The slice equality is required only almost
everywhere under the measure of the remaining coordinates.  This is
load-bearing: a Brillouin-domain identity must not be strengthened to points
outside the restricted product cube.

No CMP89 endpoint, compact integrability producer, contour estimate, `B0`,
owner dictionary or window-15 conclusion is introduced here.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Almost-everywhere version of the sealed interval-integral slice
transport. -/
theorem intervalIntegral_integral_eq_of_slice_intervalIntegral_ae_eq
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [SFinite μ] {a b : ℝ} {f g : ℝ → α → E}
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc a b)).prod μ))
    (hg : Integrable (Function.uncurry g)
      ((volume.restrict (Set.uIoc a b)).prod μ))
    (hfg : ∀ᵐ y ∂μ, (∫ x in a..b, f x y) = ∫ x in a..b, g x y) :
    (∫ x in a..b, ∫ y, f x y ∂μ) =
      ∫ x in a..b, ∫ y, g x y ∂μ := by
  rw [intervalIntegral_integral_swap hf,
    intervalIntegral_integral_swap hg]
  exact integral_congr_ae hfg

/-- Lift an almost-everywhere coordinate-slice equality to the integral over
a finite product of identical restricted interval measures. -/
theorem integral_pi_restrict_uIoc_eq_of_coordinate_intervalIntegral_ae_eq
    {n : ℕ} {a b : ℝ} (hab : a ≤ b) (i : Fin (n + 1))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : (Fin (n + 1) → ℝ) → E}
    (hf : Integrable f
      (Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc a b)))
    (hg : Integrable g
      (Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.uIoc a b)))
    (hfg : ∀ᵐ y ∂(Measure.pi fun _ : Fin n =>
        volume.restrict (Set.uIoc a b)),
      (∫ x in a..b, f (i.insertNth x y)) =
        ∫ x in a..b, g (i.insertNth x y)) :
    (∫ q, f q ∂(Measure.pi fun _ : Fin (n + 1) =>
        volume.restrict (Set.uIoc a b))) =
      ∫ q, g q ∂(Measure.pi fun _ : Fin (n + 1) =>
        volume.restrict (Set.uIoc a b)) := by
  let μ : Fin (n + 1) → Measure ℝ := fun _ =>
    volume.restrict (Set.uIoc a b)
  let ν : Fin n → Measure ℝ := fun _ =>
    volume.restrict (Set.uIoc a b)
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) :=
    measurePreserving_piFinSuccAbove μ i
  have hf' : Integrable
      (Function.uncurry fun x y => f (i.insertNth x y))
      ((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) := by
    have h := (hmp.symm.integrable_comp_emb
      e.symm.measurableEmbedding).2 hf
    simpa [μ, ν, e, Function.uncurry,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using h
  have hg' : Integrable
      (Function.uncurry fun x y => g (i.insertNth x y))
      ((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) := by
    have h := (hmp.symm.integrable_comp_emb
      e.symm.measurableEmbedding).2 hg
    simpa [μ, ν, e, Function.uncurry,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using h
  have hf_eq :
      (∫ q, f q ∂Measure.pi μ) =
        ∫ xy, f (i.insertNth xy.1 xy.2)
          ∂((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) := by
    have h := hmp.integral_comp'
      (fun xy => f (e.symm xy))
    simpa [μ, ν, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h
  have hg_eq :
      (∫ q, g q ∂Measure.pi μ) =
        ∫ xy, g (i.insertNth xy.1 xy.2)
          ∂((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) := by
    have h := hmp.integral_comp'
      (fun xy => g (e.symm xy))
    simpa [μ, ν, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h
  have htransport :=
    intervalIntegral_integral_eq_of_slice_intervalIntegral_ae_eq
      (μ := Measure.pi ν) hf' hg' hfg
  calc
    (∫ q, f q ∂Measure.pi μ) =
        ∫ xy, f (i.insertNth xy.1 xy.2)
          ∂((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) := hf_eq
    _ = ∫ x, ∫ y, f (i.insertNth x y) ∂Measure.pi ν
          ∂volume.restrict (Set.uIoc a b) := integral_prod _ hf'
    _ = ∫ x, ∫ y, g (i.insertNth x y) ∂Measure.pi ν
          ∂volume.restrict (Set.uIoc a b) := by
      simpa [intervalIntegral.integral_of_le hab,
        Set.uIoc_of_le hab] using htransport
    _ = ∫ xy, g (i.insertNth xy.1 xy.2)
          ∂((volume.restrict (Set.uIoc a b)).prod (Measure.pi ν)) :=
      (integral_prod _ hg').symm
    _ = ∫ q, g q ∂Measure.pi μ := hg_eq.symm

end

end YangMills.RG
