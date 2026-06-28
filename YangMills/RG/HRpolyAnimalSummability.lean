/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CubeLattice
import YangMills.RG.YMActivityBudgetUV

/-!
# `hRpoly` animal-summability bridges

This file closes a small but useful `hRpoly` interface gap.  The campaign had
already proved the rooted animal-count / cube-polymer summability estimate

`∑_Y q ^ #Y ≤ (1 - Δ^2 q)⁻¹`,

and the UV consumer already knew how to turn a renormalized activity bound plus
an external weight-sum hypothesis into `SingleScaleUVDecay`.  The theorems below
compose those two verified pieces, so callers no longer carry the external
`hwsum`/`hwK` obligations for the rooted-connected finite-volume polymer
geometry.

Honest scope: this does **not** prove the hard Yang--Mills raw activity estimate
or the Appendix-F with-holes renormalization theorem.  It discharges the
combinatorial summability side of the `hRpoly` pipeline and feeds the existing
single-scale and marginal-coupling consumers directly.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (r : V)

/-- Generic rooted-connected polymer weight for a bounded-degree graph. -/
abbrev rootedConnectedWeight {q : ℝ} :
    {S : Finset V // r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} → ℝ :=
  fun Y => q ^ (Y : Finset V).card

/-- **`hRpoly` bridge, graph form.**  A renormalized activity estimate on
rooted connected polymers with weight `q ^ #Y` produces the consumer-facing
`SingleScaleUVDecay` with the animal-count constant `(1 - Δ^2 q)⁻¹`.  Thus the
previously external `hwsum`/`hwK` summability obligations are discharged by
`rooted_connected_weight_summable`. -/
theorem singleScaleUVDecay_of_rootedConnected_renormalizedActivities
    {Δ : ℕ} {q A c0 κ₀ : ℝ}
    (Rsc : ℕ → ℕ → ℝ)
    (Hsharp : ℕ → ℕ →
      {S : Finset V // r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} → ℝ)
    (g : ℕ → ℝ)
    (hΔ : ∀ w, G.degree w ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hq0 : 0 ≤ q) (hCq : (Δ : ℝ) ^ 2 * q < 1)
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hact : RenormalizedHoleActivityDecay Hsharp
      (rootedConnectedWeight G r (q := q)) g A c0 κ₀) :
    SingleScaleUVDecay Rsc g (A * (1 - (Δ : ℝ) ^ 2 * q)⁻¹) c0 κ₀ := by
  classical
  exact
    singleScaleUVDecay_of_renormalizedHoleActivities_summableWeight
      Rsc Hsharp (rootedConnectedWeight G r (q := q)) g
      hA hg hR hact Summable.of_finite
      (rooted_connected_weight_summable (G := G) (r := r)
        hΔ hΔ1 hq0 hCq)

/-- Raw-activity variant of
`singleScaleUVDecay_of_rootedConnected_renormalizedActivities`.  This is the
finite direct-sum route: once a source supplies a pointwise raw activity bound on
rooted connected polymers, the animal-count theorem supplies the missing
summability and yields the scalar `SingleScaleUVDecay`. -/
theorem singleScaleUVDecay_of_rootedConnected_rawActivities
    {Δ : ℕ} {q A c0 κ₀ : ℝ}
    (Rsc : ℕ → ℕ → ℝ)
    (Hraw : ℕ → ℕ →
      {S : Finset V // r ∈ S ∧ ∀ x ∈ S, ∃ w : G.Walk r x, IsSWalk S w} → ℝ)
    (g : ℕ → ℝ)
    (hΔ : ∀ w, G.degree w ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hq0 : 0 ≤ q) (hCq : (Δ : ℝ) ^ 2 * q < 1)
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hraw : RawYMActivityDecay Hraw
      (rootedConnectedWeight G r (q := q)) g A c0 κ₀) :
    SingleScaleUVDecay Rsc g (A * (1 - (Δ : ℝ) ^ 2 * q)⁻¹) c0 κ₀ := by
  classical
  exact
    YMActivityErrorBudget.singleScaleUVDecay_of_rawYMActivityDecay_summableWeight
      Rsc Hraw (rootedConnectedWeight G r (q := q)) g
      hA hg hR hraw Summable.of_finite
      (rooted_connected_weight_summable (G := G) (r := r)
        hΔ hΔ1 hq0 hCq)

/-- **Concrete cube-lattice `hRpoly` bridge.**  The abstract graph bridge
specialized to Dimock's `M`-cube king-adjacency graph `cubeAdj d L`, with
coordination constant `Δ = 3^d`. -/
theorem singleScaleUVDecay_of_cubePolymer_renormalizedActivities
    (d L : ℕ) [NeZero L] (r : Fin d → ZMod L)
    {q A c0 κ₀ : ℝ}
    (Rsc : ℕ → ℕ → ℝ)
    (Hsharp : ℕ → ℕ →
      {S : Finset (Fin d → ZMod L) //
        r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w} → ℝ)
    (g : ℕ → ℝ)
    (hq0 : 0 ≤ q) (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * q < 1)
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hact : RenormalizedHoleActivityDecay Hsharp
      (rootedConnectedWeight (cubeAdj d L) r (q := q)) g A c0 κ₀) :
    SingleScaleUVDecay Rsc g
      (A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q)⁻¹) c0 κ₀ := by
  classical
  exact
    singleScaleUVDecay_of_rootedConnected_renormalizedActivities
      (G := cubeAdj d L) r Rsc Hsharp g
      (Δ := 3 ^ d) (q := q)
      (fun x => cubeAdj_degree_le d L x)
      (Nat.one_le_pow _ _ (by norm_num)) hq0 hCq hA hg hR hact

/-- Concrete cube-lattice raw-activity variant. -/
theorem singleScaleUVDecay_of_cubePolymer_rawActivities
    (d L : ℕ) [NeZero L] (r : Fin d → ZMod L)
    {q A c0 κ₀ : ℝ}
    (Rsc : ℕ → ℕ → ℝ)
    (Hraw : ℕ → ℕ →
      {S : Finset (Fin d → ZMod L) //
        r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w} → ℝ)
    (g : ℕ → ℝ)
    (hq0 : 0 ≤ q) (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * q < 1)
    (hA : 0 ≤ A) (hg : ∀ k, 0 ≤ g k)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hraw t k Y)
    (hraw : RawYMActivityDecay Hraw
      (rootedConnectedWeight (cubeAdj d L) r (q := q)) g A c0 κ₀) :
    SingleScaleUVDecay Rsc g
      (A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q)⁻¹) c0 κ₀ := by
  classical
  exact
    singleScaleUVDecay_of_rootedConnected_rawActivities
      (G := cubeAdj d L) r Rsc Hraw g
      (Δ := 3 ^ d) (q := q)
      (fun x => cubeAdj_degree_le d L x)
      (Nat.one_le_pow _ _ (by norm_num)) hq0 hCq hA hg hR hraw

/-- End-to-end marginal-coupling consumer for cube-polymer renormalized
activities.  Compared with `lattice_mass_gap_of_singleScaleUVDecay_marginal`,
the `SingleScaleUVDecay` hypothesis itself is produced here from the concrete
cube-polymer animal summability theorem. -/
theorem lattice_mass_gap_marginal_of_cubePolymer_renormalizedActivities
    (d L : ℕ) [NeZero L] (r : Fin d → ZMod L)
    (covIR : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ)
    (Hsharp : ℕ → ℕ →
      {S : Finset (Fin d → ZMod L) //
        r ∈ S ∧ ∀ x ∈ S, ∃ w : (cubeAdj d L).Walk r x, IsSWalk S w} → ℝ)
    (g : ℕ → ℝ)
    {C1 ε c0 β κ₀ q A : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hκ : 1 < κ₀)
    (hβ : 0 < β) (hpos : ∀ k, 0 < g k)
    (hsmall : ∀ k, β * g k < 1)
    (hrec : ∀ k, g (k + 1) = g k * (1 - β * g k))
    (hq0 : 0 ≤ q) (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * q < 1)
    (hA : 0 ≤ A)
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hact : RenormalizedHoleActivityDecay Hsharp
      (rootedConnectedWeight (cubeAdj d L) r (q := q)) g A c0 κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t|
        ≤ (C1 + (A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q)⁻¹) *
              ∑' k, g k ^ κ₀) * Real.exp (-(gap * (t : ℝ))) := by
  classical
  have hden_pos : 0 < 1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q := by linarith
  have hC2 : 0 ≤ A * (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * q)⁻¹ :=
    mul_nonneg hA (inv_nonneg.mpr hden_pos.le)
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g hε hc0 hC2 hκ hβ hpos hsmall hrec hIRbound
      (singleScaleUVDecay_of_cubePolymer_renormalizedActivities
        d L r Rsc Hsharp g hq0 hCq hA (fun k => (hpos k).le) hR hact)

end YangMills.RG
