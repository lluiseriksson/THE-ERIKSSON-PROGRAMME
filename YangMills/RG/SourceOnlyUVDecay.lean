/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.YMActivityBudgetUV

/-!
# Source-only UV profile adapters

This file records a small but useful hypothesis-removal step for the `hRpoly`
frontier.  The general `YMActivityErrorBudget` route combines a source-shaped
activity with covariance, dictionary, support, and Jacobian defect estimates.
When a future construction has no residual defects (or has already normalized
those defects definitionally to zero), the consumer should not have to carry the
four defect estimates as external obligations.

The theorems below turn a single source-profile estimate directly into the
existing `RawYMActivityDecay`, `SingleScaleUVDecay`, and marginal-coupling
mass-gap consumers.  They do not prove the source estimate itself, the
Appendix-F theorem, Eq. (2.31), `hRpoly`, a continuum limit, or Clay.  They only
remove duplicate bookkeeping hypotheses once the raw activity is source-only.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

namespace YMActivityErrorBudget

open scoped BigOperators

/-- The one-channel metric profile used by the source-only UV adapters. -/
noncomputable def sourceProfile {ι : Type*} (η : ℝ) (dist : ι → ℕ) (Y : ι) : ℝ :=
  Real.exp (-(η * (dist Y : ℝ)))

/-- The source-only metric profile is strictly positive. -/
theorem sourceProfile_pos {ι : Type*} (η : ℝ) (dist : ι → ℕ) (Y : ι) :
    0 < sourceProfile η dist Y := by
  exact Real.exp_pos _

/-- The source-only metric profile is nonnegative. -/
theorem sourceProfile_nonneg {ι : Type*} (η : ℝ) (dist : ι → ℕ) (Y : ι) :
    0 ≤ sourceProfile η dist Y :=
  (sourceProfile_pos η dist Y).le

/-- Source-only raw activity decay.

If the raw activity is exactly a source-shaped term and that term has the
source profile `exp (-η·dist)`, then the existing `RawYMActivityDecay` predicate
follows after comparing that profile to the caller's raw weight.  The four
defect estimates required by the general five-channel adapter are absent here. -/
theorem rawYMActivityDecay_of_source_profile {ι : Type*}
    (dist : ι → ℕ) (w : ι → ℝ)
    (Hraw Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ η : ℝ}
    (hA : 0 ≤ A)
    (hscale :
      ∀ t k : ℕ, 0 ≤ Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀)
    (hprofile_le : ∀ Y, sourceProfile η dist Y ≤ w Y)
    (hdecomp : ∀ t k Y, Hraw t k Y = Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y) :
    RawYMActivityDecay Hraw w g A c0 κ₀ := by
  intro t k Y
  have hcoeff :
      0 ≤ A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) :=
    mul_nonneg hA (hscale t k)
  have hweight :
      A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
          sourceProfile η dist Y ≤
        A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y :=
    mul_le_mul_of_nonneg_left (hprofile_le Y) hcoeff
  calc
    |Hraw t k Y| = |Hsource t k Y| := by rw [hdecomp t k Y]
    _ ≤ A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
          sourceProfile η dist Y := hsource t k Y
    _ ≤ A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) * w Y := hweight
    _ = A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀ * w Y := by ring

/-- Source-only raw activity decay with the common scale nonnegativity derived
from a nonnegative coupling profile. -/
theorem rawYMActivityDecay_of_source_profile_nonneg {ι : Type*}
    (dist : ι → ℕ) (w : ι → ℝ)
    (Hraw Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ η : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hprofile_le : ∀ Y, sourceProfile η dist Y ≤ w Y)
    (hdecomp : ∀ t k Y, Hraw t k Y = Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y) :
    RawYMActivityDecay Hraw w g A c0 κ₀ :=
  rawYMActivityDecay_of_source_profile dist w Hraw Hsource g hA
    (rawYMActivityScale_nonneg g c0 κ₀ hg) hprofile_le hdecomp hsource

/-- Canonical source-only raw activity decay using the source profile itself as
the raw weight. -/
theorem rawYMActivityDecay_of_source_profile_self {ι : Type*}
    (dist : ι → ℕ) (Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ η : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y) :
    RawYMActivityDecay Hsource (sourceProfile η dist) g A c0 κ₀ :=
  rawYMActivityDecay_of_source_profile_nonneg dist (sourceProfile η dist)
    Hsource Hsource g hA hg (fun _ => le_rfl) (fun _ _ _ => rfl) hsource

/-- Source-only route to the scalar single-scale UV consumer.

Compared with the five-channel route, the caller supplies only the exact scalar
sum, one source estimate, profile comparison, weight summability, and a weight
sum bound. -/
theorem singleScaleUVDecay_of_source_profile_tsum_summableWeight {ι : Type*}
    (dist : ι → ℕ) (w : ι → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (Hraw Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A K₀ c0 κ₀ η : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hprofile_le : ∀ Y, sourceProfile η dist Y ≤ w Y)
    (hdecomp : ∀ t k Y, Hraw t k Y = Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    SingleScaleUVDecay Rsc g (A * K₀) c0 κ₀ :=
  singleScaleUVDecay_of_rawYMActivityDecay_summableWeight Rsc Hraw w g
    hA hg hR
    (rawYMActivityDecay_of_source_profile_nonneg dist w Hraw Hsource g
      hA hg hprofile_le hdecomp hsource)
    hwsum hwK

/-- Finite-carrier source-only route to the scalar single-scale UV consumer.

For finite activity carriers, both profile summability and the profile-sum bound
are theorem-fed by finiteness. -/
theorem singleScaleUVDecay_of_source_profile_fintype {ι : Type*} [Fintype ι]
    (dist : ι → ℕ)
    (Rsc : ℕ → ℕ → ℝ) (Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A c0 κ₀ η : ℝ}
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y) :
    SingleScaleUVDecay Rsc g
      (A * ∑ Y : ι, sourceProfile η dist Y) c0 κ₀ := by
  exact
    singleScaleUVDecay_of_source_profile_tsum_summableWeight dist
      (sourceProfile η dist) Rsc Hsource Hsource g
      hA hg hR (fun _ => le_rfl) (fun _ _ _ => rfl) hsource
      Summable.of_finite
      (by simp [tsum_fintype])

/-- Source-only route all the way to the marginal-coupling mass-gap consumer.

The scalar side condition `0 ≤ K₀` is derived from the positive source profile
and the supplied weight-sum bound, so it is not an extra external premise. -/
theorem lattice_mass_gap_marginal_of_source_profile_tsum_summableWeight
    {ι : Type*}
    (dist : ι → ℕ) (w : ι → ℝ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hraw Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A C1 ε c0 β κ₀ K₀ η : ℝ}
    (hA : 0 ≤ A)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hprofile_le : ∀ Y, sourceProfile η dist Y ≤ w Y)
    (hdecomp : ∀ t k Y, Hraw t k Y = Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y)
    (hwsum : Summable w) (hwK : ∑' Y, w Y ≤ K₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (A * K₀) * ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  have hw_nonneg : ∀ Y, 0 ≤ w Y := by
    intro Y
    exact (sourceProfile_nonneg η dist Y).trans (hprofile_le Y)
  have hK₀ : 0 ≤ K₀ := by
    exact (tsum_nonneg hw_nonneg).trans hwK
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g
      (C2 := A * K₀)
      hε hc0 (mul_nonneg hA hK₀) hκ hβ hpos hsmall hrec hIRbound
      (singleScaleUVDecay_of_source_profile_tsum_summableWeight dist w
        Rsc Hraw Hsource g hA (fun k => (hpos k).le) hR hprofile_le
        hdecomp hsource hwsum hwK)

/-- Finite-carrier source-only marginal-coupling mass-gap route.

Finiteness discharges both the profile summability and the profile-sum bound,
leaving only the source estimate, scalar identity, IR estimate, and marginal
coupling hypotheses. -/
theorem lattice_mass_gap_marginal_of_source_profile_fintype
    {ι : Type*} [Fintype ι]
    (dist : ι → ℕ)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hsource : ℕ → ℕ → ι → ℝ) (g : ℕ → ℝ)
    {A C1 ε c0 β κ₀ η : ℝ}
    (hA : 0 ≤ A)
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsource t k Y)
    (hsource :
      ∀ t k Y,
        |Hsource t k Y| ≤
          A * (Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) *
            sourceProfile η dist Y) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (A * ∑ Y : ι, sourceProfile η dist Y) *
              ∑' k, g k ^ κ₀) *
            Real.exp (-(gap * (t : ℝ))) := by
  exact
    lattice_mass_gap_marginal_of_source_profile_tsum_summableWeight dist
      (sourceProfile η dist) covIR Rsc nsc Hsource Hsource g
      hA hε hc0 hκ hβ hpos hsmall hrec hIRbound hR
      (fun _ => le_rfl) (fun _ _ _ => rfl) hsource
      Summable.of_finite
      (by simp [tsum_fintype])

end YMActivityErrorBudget

end YangMills.RG
