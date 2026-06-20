/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.SingleScaleUVDecay
import YangMills.RG.LocalKP

/-!
# Polymer cluster-with-holes bridge

This module packages the quantitative bookkeeping that sits between the
Appendix-F with-holes activity estimate and the scalar UV `hpoly` input.

The residual decay rate after the standard Appendix-F losses is

```
polymerClusterResidualRate κ κ₀ = κ - 3 * κ₀ - 3.
```

If this residual rate still dominates the geometric summability exponent
`κ₀`, then a pointwise `H#` bound with residual decay can be summed using the
already available geometric weight `exp (-κ₀ d)`.  Equivalently, the common
condition `κ ≥ 3κ₀ + 3` proves only nonnegativity of the residual; the stronger
condition `κ ≥ 4κ₀ + 3` is enough to reuse the `κ₀`-weighted summability
substrate directly.

This is bookkeeping and summation only.  It does not prove the with-holes
cluster expansion, Dimock (642), the geometric summability hypothesis, the
concrete Yang--Mills fluctuation activity estimate, a continuum limit, or a
Clay mass gap.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Residual modified-metric decay left after the Appendix-F loss
`3κ₀ + 3`. -/
def polymerClusterResidualRate (κ κ₀ : ℝ) : ℝ :=
  κ - 3 * κ₀ - 3

/-- The usual `κ ≥ 3κ₀ + 3` condition only makes the residual decay
nonnegative. -/
theorem polymerClusterResidualRate_nonneg_of_three_mul_add_le
    {κ κ₀ : ℝ} (hκ : 3 * κ₀ + 3 ≤ κ) :
    0 ≤ polymerClusterResidualRate κ κ₀ := by
  unfold polymerClusterResidualRate
  linarith

/-- To reuse a geometric summability estimate at exponent `κ₀`, it is enough
to strengthen the source-side margin to `κ ≥ 4κ₀ + 3`. -/
theorem kappa0_le_polymerClusterResidualRate_of_four_mul_add_le
    {κ κ₀ : ℝ} (hκ : 4 * κ₀ + 3 ≤ κ) :
    κ₀ ≤ polymerClusterResidualRate κ κ₀ := by
  unfold polymerClusterResidualRate
  linarith

/-- If the residual rate dominates `κ₀`, its exponential weight is bounded by
the geometric `κ₀`-weight. -/
theorem exp_neg_residualRate_mul_le_exp_neg_kappa0_mul
    {κ κ₀ : ℝ} (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀) (n : ℕ) :
    Real.exp (-(polymerClusterResidualRate κ κ₀ * (n : ℝ))) ≤
      Real.exp (-(κ₀ * (n : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right hres hn]

/-- Rewrite the exponential metric weight into the `q^n` form consumed by the
discrete modified-metric summability theorem, with `q = exp (-κ₀)`. -/
theorem exp_neg_kappa0_nat_eq_exp_neg_pow (κ₀ : ℝ) (n : ℕ) :
    Real.exp (-(κ₀ * (n : ℝ))) = Real.exp (-κ₀) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Static aggregate bridge: a residual with-holes activity estimate plus
geometric summability at exponent `κ₀` implies the aggregate `hpoly`-style
bound `Σ |H#| ≤ C H₀ K₀`, provided `κ₀ ≤ κ - 3κ₀ - 3`. -/
theorem polymerClusterWithHoles_abs_tsum_le
    {ι : Type*} (Hsharp : ι → ℝ) (metric : ι → ℕ)
    {C H₀ K₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hact : ∀ Y,
      |Hsharp Y| ≤ C * H₀ *
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))))
    (hgeom : Summable fun Y => Real.exp (-(κ₀ * (metric Y : ℝ))))
    (hgeomK : (∑' Y, Real.exp (-(κ₀ * (metric Y : ℝ)))) ≤ K₀) :
    Summable (fun Y => |Hsharp Y|) ∧
      (∑' Y, |Hsharp Y|) ≤ C * H₀ * K₀ := by
  classical
  have hAmp : 0 ≤ C * H₀ := mul_nonneg hC hH₀
  let w : ι → ℝ := fun Y => Real.exp (-(κ₀ * (metric Y : ℝ)))
  have hpoint : ∀ Y, |Hsharp Y| ≤ C * H₀ * w Y := by
    intro Y
    calc
      |Hsharp Y| ≤ C * H₀ *
          Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))) :=
        hact Y
      _ ≤ C * H₀ * w Y := by
        exact mul_le_mul_of_nonneg_left
          (exp_neg_residualRate_mul_le_exp_neg_kappa0_mul hres (metric Y))
          hAmp
  have hmajor : Summable (fun Y => C * H₀ * w Y) := hgeom.mul_left _
  have habs : Summable (fun Y => |Hsharp Y|) :=
    hmajor.of_nonneg_of_le (fun Y => abs_nonneg (Hsharp Y)) hpoint
  refine ⟨habs, ?_⟩
  calc
    (∑' Y, |Hsharp Y|) ≤ ∑' Y, C * H₀ * w Y :=
      habs.tsum_le_tsum hpoint hmajor
    _ = C * H₀ * ∑' Y, w Y := tsum_mul_left
    _ ≤ C * H₀ * K₀ := mul_le_mul_of_nonneg_left hgeomK hAmp

/-- Concrete `κ₀`-exponential form of the already proved rooted
modified-metric summability theorem.  This is the adapter from the analytic
residual notation `exp (-κ₀(d_M+1))` to the combinatorial theorem's
`q^(d_M+1)` input with `q = exp (-κ₀)`. -/
theorem rooted_exp_discreteModifiedMetric_tsum_le
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (r : Cube d L) (κ₀ : ℝ)
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ∑' X : { X : Finset (Cube d L) //
        r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
      Real.exp (-(κ₀ *
        ((discreteModifiedMetric H (X : Finset (Cube d L)) + 1 : ℕ) : ℝ)))
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  have hsum :=
    discreteModifiedMetric_weight_summable H r (Real.exp (-κ₀))
      hdisj hnoedges hholes_ne (Real.exp_pos _).le hCq
  have hfun :
      (fun X : { X : Finset (Cube d L) //
          r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } =>
        Real.exp (-(κ₀ *
          ((discreteModifiedMetric H (X : Finset (Cube d L)) + 1 : ℕ) : ℝ)))) =
      (fun X : { X : Finset (Cube d L) //
          r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } =>
        Real.exp (-κ₀) ^
          (discreteModifiedMetric H (X : Finset (Cube d L)) + 1)) := by
    funext X
    simpa [Nat.cast_add, Nat.cast_one] using
      exp_neg_kappa0_nat_eq_exp_neg_pow κ₀
        (discreteModifiedMetric H (X : Finset (Cube d L)) + 1)
  rw [hfun]
  exact hsum

/-- Concrete rooted with-holes aggregate bridge.  A residual activity bound in
the actual modified metric, together with the coordination smallness condition
from `discreteModifiedMetric_weight_summable`, gives the `hpoly`-style rooted
aggregate estimate. -/
theorem rooted_polymerClusterWithHoles_abs_tsum_le
    {d L : ℕ} [NeZero L] (H : HoleFamily d L) (r : Cube d L)
    (Hsharp :
      { X : Finset (Cube d L) //
        r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } → ℝ)
    {C H₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hact : ∀ X,
      |Hsharp X| ≤ C * H₀ *
        Real.exp (-(polymerClusterResidualRate κ κ₀ *
          ((discreteModifiedMetric H (X : Finset (Cube d L)) + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    Summable (fun X => |Hsharp X|) ∧
      (∑' X, |Hsharp X|) ≤ C * H₀ *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  let metric :
      { X : Finset (Cube d L) //
        r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } → ℕ :=
    fun X => discreteModifiedMetric H (X : Finset (Cube d L)) + 1
  have hgeom :
      Summable fun X =>
        Real.exp (-(κ₀ * (metric X : ℝ))) :=
    Summable.of_finite
  have hgeomK :
      (∑' X, Real.exp (-(κ₀ * (metric X : ℝ)))) ≤
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
    simpa [metric] using
      rooted_exp_discreteModifiedMetric_tsum_le H r κ₀
        hdisj hnoedges hholes_ne hCq
  exact polymerClusterWithHoles_abs_tsum_le Hsharp metric hC hH₀ hres hact hgeom hgeomK

/-- Equivalence between rooted active `Ω`-polymers and the rooted concrete
modified-metric subtype.  The only additional datum in `OmegaPolymerType` is
nonempty skeleton; the root membership supplies it. -/
noncomputable def omegaRootedPolymerEquiv {d L : ℕ} [NeZero L]
    (H : HoleFamily d L) (z : Finset (Cube d L) → ℂ) (r : Cube d L) :
    { P : OmegaPolymerType H z // r ∈ skeleton H P.val } ≃
      { X : Finset (Cube d L) //
        r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X } := by
  classical
  let f := fun P : { P : OmegaPolymerType H z // r ∈ skeleton H P.val } =>
    (⟨P.val.val, ⟨P.property, P.val.property.right.left,
      P.val.property.right.right.left⟩⟩ :
      { X : Finset (Cube d L) //
        r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X })
  have hf_inj : Function.Injective f := by
    intro a b h
    have h_eq : a.val.val = b.val.val := congrArg (fun x => x.val) h
    have h_poly : a.val = b.val := Subtype.ext h_eq
    exact Subtype.ext h_poly
  have hf_surj : Function.Surjective f := by
    intro X
    have hne : X.val.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hr_sub := skeleton_subset H X.val X.property.left
      rw [he] at hr_sub
      cases hr_sub
    have hskel_ne : (skeleton H X.val).Nonempty := ⟨r, X.property.left⟩
    refine ⟨⟨⟨X.val, ⟨hne, X.property.right.left,
      X.property.right.right, hskel_ne⟩⟩, X.property.left⟩, ?_⟩
    rfl
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- `OmegaPolymerType` form of the concrete `κ₀`-exponential rooted
modified-metric summability theorem. -/
theorem omega_rooted_exp_discreteModifiedMetric_tsum_le
    {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) (r : Cube d L) (κ₀ : ℝ)
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ∑' P : { P : OmegaPolymerType H z // r ∈ skeleton H P.val },
      Real.exp (-(κ₀ *
        ((discreteModifiedMetric H (P.val.val : Finset (Cube d L)) + 1 : ℕ) : ℝ)))
      ≤ (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  let e := omegaRootedPolymerEquiv H z r
  have hsum_eq :
      ∑ P : { P : OmegaPolymerType H z // r ∈ skeleton H P.val },
        Real.exp (-(κ₀ *
          ((discreteModifiedMetric H (P.val.val : Finset (Cube d L)) + 1 : ℕ) : ℝ)))
      =
      ∑ X : { X : Finset (Cube d L) //
          r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X },
        Real.exp (-(κ₀ *
          ((discreteModifiedMetric H (X : Finset (Cube d L)) + 1 : ℕ) : ℝ))) := by
    refine Fintype.sum_equiv e _ _ ?_
    intro P
    rfl
  rw [tsum_fintype, hsum_eq]
  simpa [tsum_fintype] using
    rooted_exp_discreteModifiedMetric_tsum_le H r κ₀
      hdisj hnoedges hholes_ne hCq

/-- `OmegaPolymerType` rooted aggregate bridge.  This is the same residual
with-holes estimate as `rooted_polymerClusterWithHoles_abs_tsum_le`, but
stated directly on the source-facing active polymer type used by Appendix F
and `omegaHolePolymerSystem`. -/
theorem omega_rooted_polymerClusterWithHoles_abs_tsum_le
    {d L : ℕ} [NeZero L] (H : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ) (r : Cube d L)
    (Hsharp : { P : OmegaPolymerType H z // r ∈ skeleton H P.val } → ℝ)
    {C H₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hact : ∀ P,
      |Hsharp P| ≤ C * H₀ *
        Real.exp (-(polymerClusterResidualRate κ κ₀ *
          ((discreteModifiedMetric H (P.val.val : Finset (Cube d L)) + 1 : ℕ) : ℝ))))
    (hdisj : ∀ H₁ ∈ H.holes, ∀ H₂ ∈ H.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) H.holes)
    (hholes_ne : ∀ H₀ ∈ H.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    Summable (fun P => |Hsharp P|) ∧
      (∑' P, |Hsharp P|) ≤ C * H₀ *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
  classical
  let metric : { P : OmegaPolymerType H z // r ∈ skeleton H P.val } → ℕ :=
    fun P => discreteModifiedMetric H (P.val.val : Finset (Cube d L)) + 1
  have hgeom :
      Summable fun P =>
        Real.exp (-(κ₀ * (metric P : ℝ))) :=
    Summable.of_finite
  have hgeomK :
      (∑' P, Real.exp (-(κ₀ * (metric P : ℝ)))) ≤
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹ := by
    simpa [metric] using
      omega_rooted_exp_discreteModifiedMetric_tsum_le H z r κ₀
        hdisj hnoedges hholes_ne hCq
  exact polymerClusterWithHoles_abs_tsum_le Hsharp metric hC hH₀ hres hact hgeom hgeomK

/-- Source-facing residual with-holes activity decay.  This is the Appendix-F
output shape before using the geometric `κ₀` summability substrate. -/
def ClusterWithHolesActivityDecay {ι : Type*}
    (Hsharp : ℕ → ℕ → ι → ℝ) (metric : ι → ℕ) (g : ℕ → ℝ)
    (C H₀ c₀ κ κ₀ : ℝ) : Prop :=
  ∀ t k Y,
    |Hsharp t k Y| ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ)))

/-- If the residual decay dominates `κ₀`, the residual with-holes activity
decay is a `RenormalizedHoleActivityDecay` with geometric weight
`exp (-κ₀ d)`. -/
theorem renormalizedHoleActivityDecay_of_clusterWithHolesActivityDecay
    {ι : Type*}
    (Hsharp : ℕ → ℕ → ι → ℝ) (metric : ι → ℕ) (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hact : ClusterWithHolesActivityDecay Hsharp metric g C H₀ c₀ κ κ₀) :
    RenormalizedHoleActivityDecay Hsharp
      (fun Y => Real.exp (-(κ₀ * (metric Y : ℝ)))) g
      (C * H₀) c₀ κ₀ := by
  intro t k Y
  have hscale :
      0 ≤ C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC hH₀) (Real.exp_pos _).le)
      (Real.rpow_nonneg (hg k) κ₀)
  calc
    |Hsharp t k Y| ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp (-(polymerClusterResidualRate κ κ₀ * (metric Y : ℝ))) :=
      hact t k Y
    _ ≤ C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp (-(κ₀ * (metric Y : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (exp_neg_residualRate_mul_le_exp_neg_kappa0_mul hres (metric Y))
        hscale
    _ = (C * H₀) * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp (-(κ₀ * (metric Y : ℝ))) := by
      ring

/-- Full producer bridge to the scalar `SingleScaleUVDecay` consumer: residual
with-holes decay plus `κ₀`-geometric summability gives the scalar per-scale UV
decay with amplitude `(C * H₀) * K₀`.  Absolute summability of the activity
sum is derived from the same geometric majorant. -/
theorem singleScaleUVDecay_of_clusterWithHolesActivities
    {ι : Type*}
    (Rsc : ℕ → ℕ → ℝ) (Hsharp : ℕ → ℕ → ι → ℝ)
    (metric : ι → ℕ) (g : ℕ → ℝ)
    {C H₀ K₀ c₀ κ κ₀ : ℝ}
    (hC : 0 ≤ C) (hH₀ : 0 ≤ H₀) (hg : ∀ k, 0 ≤ g k)
    (hres : κ₀ ≤ polymerClusterResidualRate κ κ₀)
    (hR : ∀ t k, Rsc t k = ∑' Y, Hsharp t k Y)
    (hact : ClusterWithHolesActivityDecay Hsharp metric g C H₀ c₀ κ κ₀)
    (hgeom : Summable fun Y => Real.exp (-(κ₀ * (metric Y : ℝ))))
    (hgeomK : (∑' Y, Real.exp (-(κ₀ * (metric Y : ℝ)))) ≤ K₀) :
    SingleScaleUVDecay Rsc g ((C * H₀) * K₀) c₀ κ₀ := by
  classical
  let w : ι → ℝ := fun Y => Real.exp (-(κ₀ * (metric Y : ℝ)))
  have hren :
      RenormalizedHoleActivityDecay Hsharp w g (C * H₀) c₀ κ₀ := by
    simpa [w] using
      renormalizedHoleActivityDecay_of_clusterWithHolesActivityDecay
        Hsharp metric g hC hH₀ hg hres hact
  have hHsummable : ∀ t k, Summable (fun Y => |Hsharp t k Y|) := by
    intro t k
    have hmajor :
        Summable
          (fun Y => ((C * H₀) * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) * w Y) :=
      by
        simpa [w] using
          hgeom.mul_left
            ((C * H₀) * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀)
    exact hmajor.of_nonneg_of_le
      (fun Y => abs_nonneg (Hsharp t k Y))
      (fun Y => by
        have hY := hren t k Y
        simpa [w, mul_assoc] using hY)
  simpa [mul_assoc] using
    singleScaleUVDecay_of_renormalizedHoleActivities
      Rsc Hsharp w g (hA := mul_nonneg hC hH₀) hg hR hHsummable
      hren (by simpa [w] using hgeom) (by simpa [w] using hgeomK)

end YangMills.RG
