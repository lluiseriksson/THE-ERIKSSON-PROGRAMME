/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.UVMassGap
import YangMills.RG.PolymerRemainder

/-!
# Semantic interfaces for single-scale UV decay

The lattice mass-gap assembly ultimately consumes a scalar per-scale bound

`|Rsc t k| ≤ A * exp (-(c0 * t)) * g k ^ κ₀`.

The polymer/Appendix-F route is one producer of that scalar estimate, but not
the only conceivable one.  This file separates the consumer-facing predicate
`SingleScaleUVDecay` from the renormalized with-holes activity producer.

Honest scope: this file does not prove Appendix F, the Yang--Mills fluctuation
integral, or a direct covariance identity.  It proves only the real summation
bridge from renormalized activities plus a weight summability bound to the
scalar single-scale decay consumed by `UVMassGap`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Consumer-facing scalar single-scale UV decay.  This is the shape used by
the UV mass-gap assembly. -/
def SingleScaleUVDecay (Rsc : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (A c0 κ₀ : ℝ) : Prop :=
  ∀ t k : ℕ, |Rsc t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀

/-- Source-facing raw Yang--Mills activity decay.  This is the pre-renormalized
activity profile one expects from the fluctuation integral.  It is deliberately
only a predicate: proving it for the concrete gauge RG operator is the hard
P4 input. -/
def RawYMActivityDecay {ι : Type*} (Hraw : ℕ → ℕ → ι → ℝ) (w : ι → ℝ)
    (g : ℕ → ℝ) (A c0 κ₀ : ℝ) : Prop :=
  ∀ t k Y, |Hraw t k Y| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ * w Y

/-- Source-facing renormalized with-holes activity decay.  This is the
Appendix-F output shape after the with-holes cluster expansion has produced
renormalized activities. -/
def RenormalizedHoleActivityDecay {ι : Type*} (Hsharp : ℕ → ℕ → ι → ℝ)
    (w : ι → ℝ) (g : ℕ → ℝ) (A c0 κ₀ : ℝ) : Prop :=
  ∀ t k Y, |Hsharp t k Y| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ * w Y

/-- The Appendix-F/with-holes producer of the consumer-facing scalar UV decay.

If the scalar remainder `Rsc t k` is the absolutely summable sum of
renormalized activities `Hsharp t k Y`, each activity obeys the modified-metric
profile with weight `w`, and `∑ w ≤ K₀`, then the scalar single-scale decay
holds with amplitude `A * K₀`.

This is a genuine bridge: it uses the already-proved
`polymer_remainder_bound`, not a restatement of `SingleScaleUVDecay`. -/
theorem singleScaleUVDecay_of_renormalizedHoleActivities {ι : Type*}
    (Rsc : ℕ → ℕ → ℝ) (Hsharp : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A K₀ c0 κ₀ : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hHsummable : ∀ t k, Summable (fun Y => |Hsharp t k Y|))
    (hact : RenormalizedHoleActivityDecay Hsharp w g A c0 κ₀)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (A * K₀) c0 κ₀ := by
  intro t k
  have hAt : 0 ≤ A * Real.exp (-(c0 * (t : ℝ))) :=
    mul_nonneg hA (Real.exp_pos _).le
  have hpoly := polymer_remainder_bound (κ₀ := κ₀)
    (fun k => Rsc t k) (fun k Y => Hsharp t k Y) w g
    hAt hg (fun k => hR t k) (fun k => hHsummable t k) ?_ hwsum hwK k
  · calc
      |Rsc t k| ≤ (A * Real.exp (-(c0 * (t : ℝ)))) * K₀ * g k ^ κ₀ := hpoly
      _ = (A * K₀) * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ := by ring
  · intro k Y
    calc
      |Hsharp t k Y| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ * w Y :=
        hact t k Y
      _ = (A * Real.exp (-(c0 * (t : ℝ)))) * g k ^ κ₀ * w Y := by ring

/-- Absolute summability of renormalized with-holes activities follows from
their pointwise decay against a summable weight.

This is only downstream bookkeeping: it does not prove the activity decay
estimate or the weight summability theorem. -/
theorem summable_abs_of_renormalizedHoleActivityDecay {ι : Type*}
    (Hsharp : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ : ℝ}
    (hact : RenormalizedHoleActivityDecay Hsharp w g A c0 κ₀)
    (hwsum : Summable w) :
    ∀ t k, Summable (fun Y => |Hsharp t k Y|) := by
  intro t k
  have hmajor :
      Summable
        (fun Y => (A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y) :=
    hwsum.mul_left _
  exact hmajor.of_nonneg_of_le
    (fun Y => abs_nonneg (Hsharp t k Y))
    (fun Y => by
      have hY := hact t k Y
      simpa [mul_assoc] using hY)

/-- Scalar UV decay from renormalized with-holes activity decay, deriving the
absolute summability premise from the same pointwise decay and summable weight.

The exact scalar identity `Rsc = tsum Hsharp`, weight summability, and
weight-sum bound remain explicit hypotheses. -/
theorem singleScaleUVDecay_of_renormalizedHoleActivities_summableWeight
    {ι : Type*}
    (Rsc : ℕ → ℕ → ℝ) (Hsharp : ℕ → ℕ → ι → ℝ) (w : ι → ℝ) (g : ℕ → ℝ)
    {A K₀ c0 κ₀ : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hact : RenormalizedHoleActivityDecay Hsharp w g A c0 κ₀)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (A * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_renormalizedHoleActivities Rsc Hsharp w g
    hA hg hR
    (summable_abs_of_renormalizedHoleActivityDecay Hsharp w g hact hwsum)
    hact hwsum hwK

/-- Geometric-coupling mass-gap assembly expressed through the named
`SingleScaleUVDecay` predicate. -/
theorem lattice_mass_gap_of_singleScaleUVDecay_geometric
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ) (g : ℕ → ℝ)
    {C1 ε c0 A C r κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hr0 : 0 < r) (hr1 : r < 1) (hκ : 1 ≤ κ₀)
    (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g k ≤ C * r ^ k)
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hUV : SingleScaleUVDecay Rsc g A c0 κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + A * C ^ κ₀ * (1 - r)⁻¹) * Real.exp (-(gap * (t : ℝ))) :=
  lattice_mass_gap_of_cluster_and_coupling covIR Rsc nsc g
    hε hc0 hA hC hr0 hr1 hκ hg0 hg hIRbound hUV

end YangMills.RG
