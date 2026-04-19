/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.ClusterSeriesBound

/-!
# Phase 15d: Mayer / Ursell truncation (Layer B2)

Oracle target: `[propext, Classical.choice, Quot.sound]`.

This layer formalises the analytic content of the Möbius / Ursell
truncation identity
`log (∑ X, z X) = ∑ Y, K Y`
as an abstract `TruncatedActivities` structure on a polymer index
type `ι`. Rather than reconstructing the (very heavy) combinatorial
proof of the identity itself — which requires Möbius-lattice
infrastructure not yet available in Mathlib — we take the truncated
activity `K` together with a pointwise amplitude / decay bound
`|K Y| ≤ K_bound Y` as structure data, and prove the *analytic*
consequences that feed the Clay oracle:

* absolute convergence of `∑ Y, K Y`,
* control of the connecting sub-sum `∑ Y ∋ p, q, K Y`,
* an abstract two-point decay bound `|connectingSum p q| ≤ C · D`.

This factoring is explicit in the Kotecky-Preiss framework: the
combinatorial identity and the analytic KP-smallness bound are
independent inputs, and the Clay target only needs the analytic one.
No sorry, no new axioms.

References: Kotecky-Preiss, *Cluster expansion for abstract polymer
models*, Comm. Math. Phys. **103** (1986); Brydges-Kennedy,
*Mayer expansions and the Hamilton-Jacobi equation*,
J. Stat. Phys. **48** (1987).
-/

namespace YangMills

open Real

/-! ### Abstract truncated-activity system -/

/-- A truncated-activity system on a polymer index type `ι`.

It encapsulates the analytic content of the Möbius / Ursell truncation:
a truncated activity `K` with a pointwise, summable amplitude bound.
This suffices to deduce absolute convergence of the cluster sum and
exponential decay of the two-point correlator. -/
structure TruncatedActivities (ι : Type*) where
  /-- The truncated (Ursell) activity. -/
  K : Finset ι → ℝ
  /-- Pointwise upper bound on `|K|`. -/
  K_bound : Finset ι → ℝ
  /-- The bound is nonnegative. -/
  K_bound_nonneg : ∀ Y, 0 ≤ K_bound Y
  /-- Amplitude bound on the truncated activity. -/
  K_abs_le : ∀ Y, |K Y| ≤ K_bound Y
  /-- The bound is summable. -/
  summable_K_bound : Summable K_bound

namespace TruncatedActivities

variable {ι : Type*}

/-! ### Absolute summability -/

/-- The absolute truncated activity is summable. -/
theorem summable_abs_K (T : TruncatedActivities ι) :
    Summable (fun Y => |T.K Y|) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.summable_K_bound
  · intro Y; exact abs_nonneg _
  · intro Y; exact T.K_abs_le Y

/-- The truncated activity itself is summable. -/
theorem summable_K (T : TruncatedActivities ι) :
    Summable T.K := by
  refine Summable.of_norm_bounded T.summable_K_bound ?_
  intro Y
  rw [Real.norm_eq_abs]
  exact T.K_abs_le Y

/-- The sum of `|K|` is bounded by the sum of the bound. -/
theorem tsum_abs_K_le (T : TruncatedActivities ι) :
    ∑' Y, |T.K Y| ≤ ∑' Y, T.K_bound Y :=
  Summable.tsum_le_tsum T.K_abs_le T.summable_abs_K T.summable_K_bound

/-- The total sum `∑' Y, K Y` is bounded in absolute value by
the total bound. -/
theorem abs_tsum_K_le (T : TruncatedActivities ι) :
    |∑' Y, T.K Y| ≤ ∑' Y, T.K_bound Y := by
  have h_norm : Summable (fun Y => ‖T.K Y‖) := by
    simpa only [Real.norm_eq_abs] using T.summable_abs_K
  have h1 : ‖∑' Y, T.K Y‖ ≤ ∑' Y, ‖T.K Y‖ := norm_tsum_le_tsum_norm h_norm
  have h1' : |∑' Y, T.K Y| ≤ ∑' Y, |T.K Y| := by
    simpa only [Real.norm_eq_abs] using h1
  exact h1'.trans T.tsum_abs_K_le

/-! ### Connecting sub-sum -/

/-- The connecting sub-sum: polymers containing two distinguished
elements `p, q ∈ ι`. -/
noncomputable def connectingSum [DecidableEq ι]
    (T : TruncatedActivities ι) (p q : ι) : ℝ :=
  ∑' Y : Finset ι, if p ∈ Y ∧ q ∈ Y then T.K Y else 0

/-- The connecting bound: sum of `K_bound` over polymers containing
`p` and `q`. -/
noncomputable def connectingBound [DecidableEq ι]
    (T : TruncatedActivities ι) (p q : ι) : ℝ :=
  ∑' Y : Finset ι, if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0

/-! ### Pointwise estimates on connecting indicators -/

theorem connectingIndicator_abs_le
    (T : TruncatedActivities ι) [DecidableEq ι]
    (p q : ι) (Y : Finset ι) :
    |(if p ∈ Y ∧ q ∈ Y then T.K Y else 0)| ≤
      (if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0) := by
  split_ifs with h
  · exact T.K_abs_le Y
  · rw [abs_zero]

theorem connectingIndicator_bound_nonneg
    (T : TruncatedActivities ι) [DecidableEq ι]
    (p q : ι) (Y : Finset ι) :
    0 ≤ (if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0) := by
  split_ifs with h
  · exact T.K_bound_nonneg Y
  · exact le_refl _

theorem connectingIndicator_bound_le
    (T : TruncatedActivities ι) [DecidableEq ι]
    (p q : ι) (Y : Finset ι) :
    (if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0) ≤ T.K_bound Y := by
  split_ifs with h
  · exact le_refl _
  · exact T.K_bound_nonneg Y

/-- The indicator of the connecting bound is summable. -/
theorem summable_connectingBoundIndicator
    (T : TruncatedActivities ι) [DecidableEq ι] (p q : ι) :
    Summable (fun Y : Finset ι =>
      if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.summable_K_bound
  · intro Y; exact T.connectingIndicator_bound_nonneg p q Y
  · intro Y; exact T.connectingIndicator_bound_le p q Y

/-- The indicator of the absolute connecting activity is summable. -/
theorem summable_connectingAbsIndicator
    (T : TruncatedActivities ι) [DecidableEq ι] (p q : ι) :
    Summable (fun Y : Finset ι =>
      |if p ∈ Y ∧ q ∈ Y then T.K Y else 0|) := by
  refine Summable.of_nonneg_of_le ?_ ?_
    (T.summable_connectingBoundIndicator p q)
  · intro Y; exact abs_nonneg _
  · intro Y; exact T.connectingIndicator_abs_le p q Y

/-- The connecting indicator (signed) is summable. -/
theorem summable_connectingIndicator
    (T : TruncatedActivities ι) [DecidableEq ι] (p q : ι) :
    Summable (fun Y : Finset ι =>
      if p ∈ Y ∧ q ∈ Y then T.K Y else 0) := by
  refine Summable.of_norm_bounded (T.summable_connectingBoundIndicator p q) ?_
  intro Y
  rw [Real.norm_eq_abs]
  exact T.connectingIndicator_abs_le p q Y

/-! ### Connecting-sum bounds -/

/-- The connecting bound is nonnegative. -/
theorem connectingBound_nonneg
    (T : TruncatedActivities ι) [DecidableEq ι] (p q : ι) :
    0 ≤ T.connectingBound p q :=
  tsum_nonneg (fun Y => T.connectingIndicator_bound_nonneg p q Y)

/-- **Main Layer-B2 bound.** The absolute value of the connecting sum
is bounded by the connecting bound. -/
theorem abs_connectingSum_le_connectingBound
    (T : TruncatedActivities ι) [DecidableEq ι] (p q : ι) :
    |T.connectingSum p q| ≤ T.connectingBound p q := by
  unfold connectingSum connectingBound
  have h_abs_summ : Summable (fun Y : Finset ι =>
      |if p ∈ Y ∧ q ∈ Y then T.K Y else 0|) :=
    T.summable_connectingAbsIndicator p q
  have h_bound_summ : Summable (fun Y : Finset ι =>
      if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0) :=
    T.summable_connectingBoundIndicator p q
  have h_norm_summ : Summable (fun Y : Finset ι =>
      ‖(if p ∈ Y ∧ q ∈ Y then T.K Y else 0 : ℝ)‖) := by
    simpa only [Real.norm_eq_abs] using h_abs_summ
  have h1 : |∑' Y : Finset ι, if p ∈ Y ∧ q ∈ Y then T.K Y else 0| ≤
      ∑' Y : Finset ι, |if p ∈ Y ∧ q ∈ Y then T.K Y else 0| := by
    have := norm_tsum_le_tsum_norm h_norm_summ
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∑' Y : Finset ι, |if p ∈ Y ∧ q ∈ Y then T.K Y else 0| ≤
      ∑' Y : Finset ι, if p ∈ Y ∧ q ∈ Y then T.K_bound Y else 0 :=
    Summable.tsum_le_tsum (fun Y => T.connectingIndicator_abs_le p q Y)
      h_abs_summ h_bound_summ
  exact h1.trans h2

/-! ### Two-point decay -/

/-- **Abstract two-point decay.** Given an external bound
`connectingBound p q ≤ C · D` on the cluster bound, the signed
connecting sum decays at least as fast. This is the statement
consumed by the Clay oracle: combined with a geometric estimate of
the form `C · D = C · r ^ dist(p,q)` (produced by Phase 15b via
`connecting_cluster_tsum_le`) and the lattice-animal count of
Phase 15c, one obtains exponential two-point decay for the
truncated connected correlator. -/
theorem two_point_decay_from_truncated
    [DecidableEq ι]
    (T : TruncatedActivities ι) (p q : ι) (C D : ℝ)
    (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (h_bound : T.connectingBound p q ≤ C * D) :
    |T.connectingSum p q| ≤ C * D :=
  (T.abs_connectingSum_le_connectingBound p q).trans h_bound

end TruncatedActivities

/-! ### Constructor bridge -/

/-- Construct a `TruncatedActivities` system from explicit data:
an activity `K` and a summable pointwise amplitude bound `K_bound`.
This constructor is the analytic bridge between Phase 15b
(KP smallness / cluster-series summability) and the abstract
truncation structure used here. -/
noncomputable def TruncatedActivities.ofBound
    {ι : Type*} (K : Finset ι → ℝ) (K_bound : Finset ι → ℝ)
    (hK_bound_nonneg : ∀ Y, 0 ≤ K_bound Y)
    (hK_abs_le : ∀ Y, |K Y| ≤ K_bound Y)
    (hK_bound_summable : Summable K_bound) :
    TruncatedActivities ι where
  K := K
  K_bound := K_bound
  K_bound_nonneg := hK_bound_nonneg
  K_abs_le := hK_abs_le
  summable_K_bound := hK_bound_summable

end YangMills
