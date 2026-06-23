/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondGas
import YangMills.RG.ClusterDecay
import YangMills.KP.MayerInversion

/-!
# Appendix F: the second Ursell activity `H#`

This module defines the union-fiber Ursell activity attached to the second
Appendix-F hard-core gas.  It is intentionally definition-level infrastructure:
the outer `tsum` is Lean's totalized infinite sum, not by itself a convergence
claim.  Convergence, the source residual estimate, and the real scalar
remainder identity stay as explicit later hypotheses.

The indexing matches the repository's `KP.clusterSum` convention: clusters of
size `n + 1` carry the coefficient `1/(n+1)!`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- The fixed-size union-fiber contribution to the Appendix-F second Ursell
activity.  Only tuples whose full omega-cluster union is the requested target
`Y` contribute. -/
noncomputable def appendixFHoleHsharpTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℂ :=
  (((n + 1).factorial : ℂ))⁻¹ *
    ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
      if omegaClusterUnion HF zK X = Y then
        (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
          ∏ i, (omegaHolePolymerSystem HF zK).activity (X i)
      else
        0

/-- Equivalent finite-fiber form of `appendixFHoleHsharpTerm`. -/
theorem appendixFHoleHsharpTerm_eq_sum_filter
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) :
    appendixFHoleHsharpTerm HF zK Y n =
      (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
              (fun X => omegaClusterUnion HF zK X = Y),
          (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
            ∏ i, (omegaHolePolymerSystem HF zK).activity (X i) := by
  classical
  unfold appendixFHoleHsharpTerm
  rw [Finset.sum_filter]

/-- If no tuple of size `n + 1` has union `Y`, the corresponding finite
`H#` term vanishes. -/
theorem appendixFHoleHsharpTerm_eq_zero_of_no_union
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (hY : ∀ X : Fin (n + 1) → OmegaPolymerType HF zK,
      omegaClusterUnion HF zK X ≠ Y) :
    appendixFHoleHsharpTerm HF zK Y n = 0 := by
  classical
  simp [appendixFHoleHsharpTerm, hY]

/-- The `Ω`-cluster Ursell coefficient is independent of the scalar activity
attached to the same active with-holes polymer carrier. -/
theorem omegaHolePolymerSystem_ursell_eq
    (HF : HoleFamily d L)
    (z₁ z₂ : Finset (Cube d L) → ℂ)
    {n : ℕ}
    (X : Fin n → OmegaPolymerType HF z₁) :
    KP.ursell (omegaHolePolymerSystem HF z₁) X =
      KP.ursell (omegaHolePolymerSystem HF z₂) X := by
  rfl

/-- A fixed-size `H#` fiber term only depends on the second-gas activity on
component polymers contained in the declared target union. -/
theorem appendixFHoleHsharpTerm_eq_of_activity_eq_on_union
    (HF : HoleFamily d L)
    (z₁ z₂ : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (hz :
      ∀ X : OmegaPolymerType HF z₁, X.val ⊆ Y → z₁ X.val = z₂ X.val) :
    appendixFHoleHsharpTerm HF z₁ Y n =
      appendixFHoleHsharpTerm HF z₂ Y n := by
  classical
  unfold appendixFHoleHsharpTerm
  congr 1
  refine Finset.sum_congr rfl ?_
  intro X _hX
  by_cases hXY : omegaClusterUnion HF z₁ X = Y
  · have hXY₂ : omegaClusterUnion HF z₂ X = Y := by
      simpa [omegaClusterUnion] using hXY
    have hXsub : ∀ i, (X i).val ⊆ Y := fun i =>
      omegaClusterUnion_component_subset_of_eq HF z₁ X Y i hXY
    have hursell :
        KP.ursell (omegaHolePolymerSystem HF z₁) X =
          KP.ursell (omegaHolePolymerSystem HF z₂) X :=
      omegaHolePolymerSystem_ursell_eq HF z₁ z₂ X
    have hprod :
        (∏ i, (omegaHolePolymerSystem HF z₁).activity (X i)) =
          (∏ i, (omegaHolePolymerSystem HF z₂).activity (X i)) := by
      refine Finset.prod_congr rfl ?_
      intro i _hi
      exact hz (X i) (hXsub i)
    simp [hXY, hXY₂]
    rw [hursell, hprod]
  · have hXY₂ : omegaClusterUnion HF z₂ X ≠ Y := by
      simpa [omegaClusterUnion] using hXY
    simp [hXY, hXY₂]

/-- Active-skeleton variant of
`appendixFHoleHsharpTerm_eq_of_activity_eq_on_union`. -/
theorem appendixFHoleHsharpTerm_eq_of_activity_eq_on_skeleton
    (HF : HoleFamily d L)
    (z₁ z₂ : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (hz :
      ∀ X : OmegaPolymerType HF z₁,
        skeleton HF X.val ⊆ skeleton HF Y → z₁ X.val = z₂ X.val) :
    appendixFHoleHsharpTerm HF z₁ Y n =
      appendixFHoleHsharpTerm HF z₂ Y n := by
  classical
  unfold appendixFHoleHsharpTerm
  congr 1
  refine Finset.sum_congr rfl ?_
  intro X _hX
  by_cases hXY : omegaClusterUnion HF z₁ X = Y
  · have hXY₂ : omegaClusterUnion HF z₂ X = Y := by
      simpa [omegaClusterUnion] using hXY
    have hXsub : ∀ i, skeleton HF (X i).val ⊆ skeleton HF Y := fun i =>
      omegaClusterUnion_component_skeleton_subset_of_eq HF z₁ X Y i hXY
    have hursell :
        KP.ursell (omegaHolePolymerSystem HF z₁) X =
          KP.ursell (omegaHolePolymerSystem HF z₂) X :=
      omegaHolePolymerSystem_ursell_eq HF z₁ z₂ X
    have hprod :
        (∏ i, (omegaHolePolymerSystem HF z₁).activity (X i)) =
          (∏ i, (omegaHolePolymerSystem HF z₂).activity (X i)) := by
      refine Finset.prod_congr rfl ?_
      intro i _hi
      exact hz (X i) (hXsub i)
    simp [hXY, hXY₂]
    rw [hursell, hprod]
  · have hXY₂ : omegaClusterUnion HF z₂ X ≠ Y := by
      simpa [omegaClusterUnion] using hXY
    simp [hXY, hXY₂]

/-- Summing the fixed-size union-fiber terms over every target recovers the
fixed-size term of the ordinary KP cluster sum for the second gas.  This is a
finite identity only; exchanging this finite target sum with the outer `tsum`
requires a separate summability theorem. -/
theorem sum_appendixFHoleHsharpTerm_eq_clusterSum_term
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (n : ℕ) :
    (∑ Y : Finset (Cube d L), appendixFHoleHsharpTerm HF zK Y n) =
      (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
          (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
            ∏ i, (omegaHolePolymerSystem HF zK).activity (X i) := by
  classical
  let c : ℂ := (((n + 1).factorial : ℂ))⁻¹
  let f : (Fin (n + 1) → OmegaPolymerType HF zK) → ℂ := fun X =>
    (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
      ∏ i, (omegaHolePolymerSystem HF zK).activity (X i)
  calc
    (∑ Y : Finset (Cube d L), appendixFHoleHsharpTerm HF zK Y n)
        =
      ∑ Y : Finset (Cube d L),
        c * ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
          if omegaClusterUnion HF zK X = Y then f X else 0 := by
          rfl
    _ =
      c * ∑ Y : Finset (Cube d L),
        ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
          if omegaClusterUnion HF zK X = Y then f X else 0 := by
          rw [Finset.mul_sum]
    _ =
      c * ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
        ∑ Y : Finset (Cube d L),
          if omegaClusterUnion HF zK X = Y then f X else 0 := by
          rw [Finset.sum_comm]
    _ =
      c * ∑ X : Fin (n + 1) → OmegaPolymerType HF zK, f X := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro X _hX
          rw [Finset.sum_eq_single (omegaClusterUnion HF zK X)]
          · simp
          · intro Y _hY hYne
            simp [hYne.symm]
          · intro hnot
            exact (hnot (Finset.mem_univ _)).elim
    _ =
      (((n + 1).factorial : ℂ))⁻¹ *
        ∑ X : Fin (n + 1) → OmegaPolymerType HF zK,
          (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
            ∏ i, (omegaHolePolymerSystem HF zK).activity (X i) := by
          rfl

/-- The union-fiber Appendix-F second Ursell activity.  This pins down the
formal object; convergence and identification with a logarithm/partition
function must be supplied separately. -/
noncomputable def appendixFHoleHsharp
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L)) : ℂ :=
  ∑' n : ℕ, appendixFHoleHsharpTerm HF zK Y n

/-- The totalized `H#` object only depends on the second-gas activity on
component polymers contained in the declared target union.  This is a purely
termwise `tsum` congruence, not a convergence theorem. -/
theorem appendixFHoleHsharp_eq_of_activity_eq_on_union
    (HF : HoleFamily d L)
    (z₁ z₂ : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (hz :
      ∀ X : OmegaPolymerType HF z₁, X.val ⊆ Y → z₁ X.val = z₂ X.val) :
    appendixFHoleHsharp HF z₁ Y = appendixFHoleHsharp HF z₂ Y := by
  unfold appendixFHoleHsharp
  exact tsum_congr (fun n =>
    appendixFHoleHsharpTerm_eq_of_activity_eq_on_union HF z₁ z₂ Y n hz)

/-- Active-skeleton variant of
`appendixFHoleHsharp_eq_of_activity_eq_on_union`. -/
theorem appendixFHoleHsharp_eq_of_activity_eq_on_skeleton
    (HF : HoleFamily d L)
    (z₁ z₂ : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (hz :
      ∀ X : OmegaPolymerType HF z₁,
        skeleton HF X.val ⊆ skeleton HF Y → z₁ X.val = z₂ X.val) :
    appendixFHoleHsharp HF z₁ Y = appendixFHoleHsharp HF z₂ Y := by
  unfold appendixFHoleHsharp
  exact tsum_congr (fun n =>
    appendixFHoleHsharpTerm_eq_of_activity_eq_on_skeleton HF z₁ z₂ Y n hz)

/-- The actual `H#` object obtained by feeding the evaluated `K#` activity into
the second Ursell layer. -/
noncomputable def appendixFHoleHsharpOfKsharp
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : MeasureTheory.Measure β)
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFHoleHsharp HF
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ) Y

@[simp] theorem appendixFHoleHsharpOfKsharp_eq
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : MeasureTheory.Measure β)
    (ψ : ∀ x, Ψ x)
    (Y : Finset (Cube d L)) :
    appendixFHoleHsharpOfKsharp HF z Λ Hraw μ ψ Y =
      appendixFHoleHsharp HF
        (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ) Y := rfl

/-- The evaluated `K#` specialization of `H#` only depends on spectator fields
inside the declared target union, provided each raw one-polymer activity has
spectator support inside its full source polymer. -/
theorem appendixFHoleHsharpOfKsharp_eq_of_agreeOn
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : MeasureTheory.Measure β)
    (Y : Finset (Cube d L))
    (hsub : ∀ X, X ∈ Λ → (Hraw X).spectatorSupport ⊆ X.val)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn Y ψ₁ ψ₂) :
    appendixFHoleHsharpOfKsharp HF z Λ Hraw μ ψ₁ Y =
      appendixFHoleHsharpOfKsharp HF z Λ Hraw μ ψ₂ Y := by
  exact appendixFHoleHsharp_eq_of_activity_eq_on_union
    HF
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ₁)
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ₂)
    Y
    (fun X hXY =>
      appendixFHoleSecondGasActivity_eq_of_agreeOn
        HF z Λ Hraw μ X.val hsub
        (fun x hx => hψ x (hXY hx)))

/-- Active-skeleton version of
`appendixFHoleHsharpOfKsharp_eq_of_agreeOn`. -/
theorem appendixFHoleHsharpOfKsharp_eq_of_agreeOn_skeleton
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : MeasureTheory.Measure β)
    (Y : Finset (Cube d L))
    (hHsub : ∀ X, X ∈ Λ → (Hraw X).spectatorSupport ⊆ skeleton HF X.val)
    {ψ₁ ψ₂ : ∀ x, Ψ x}
    (hψ : AgreeOn (skeleton HF Y) ψ₁ ψ₂) :
    appendixFHoleHsharpOfKsharp HF z Λ Hraw μ ψ₁ Y =
      appendixFHoleHsharpOfKsharp HF z Λ Hraw μ ψ₂ Y := by
  exact appendixFHoleHsharp_eq_of_activity_eq_on_skeleton
    HF
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ₁)
    (appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ₂)
    Y
    (fun X hXY =>
      appendixFHoleSecondGasActivity_eq_of_agreeOn_skeleton
        HF z Λ Hraw μ X.val hHsub
        (fun x hx => hψ x (hXY hx)))

/-- The scalar `H#` object obtained after integrating both the fluctuation
field and the spectator field in the first Appendix-F activity.  This is the
normal-form `z_K` input expected by the source-facing `H#` majorant layer. -/
noncomputable def appendixFHoleHsharpOfIntegratedKsharp
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : MeasureTheory.Measure γ)
    (ν : MeasureTheory.Measure β)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFHoleHsharp HF
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν) Y

@[simp] theorem appendixFHoleHsharpOfIntegratedKsharp_eq
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : MeasureTheory.Measure γ)
    (ν : MeasureTheory.Measure β)
    (Y : Finset (Cube d L)) :
    appendixFHoleHsharpOfIntegratedKsharp HF z Λ Hraw μ ν Y =
      appendixFHoleHsharp HF
        (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν) Y := rfl

/-- The spectator-integrated `K#` specialization of `H#` only depends on the
integrated second-gas scalar activity on component polymers contained in the
declared target union.  Since both spectator and fluctuation fields have already
been integrated out, this is an extensional scalar-activity wrapper rather than
a new field-agreement theorem. -/
theorem appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw₁ Hraw₂ :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : MeasureTheory.Measure γ)
    (ν : MeasureTheory.Measure β)
    (Y : Finset (Cube d L))
    (hz :
      ∀ X : OmegaPolymerType HF
          (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν),
        X.val ⊆ Y →
          appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν X.val =
            appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₂ μ ν X.val) :
    appendixFHoleHsharpOfIntegratedKsharp HF z Λ Hraw₁ μ ν Y =
      appendixFHoleHsharpOfIntegratedKsharp HF z Λ Hraw₂ μ ν Y := by
  exact appendixFHoleHsharp_eq_of_activity_eq_on_union
    HF
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν)
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₂ μ ν)
    Y hz

/-- Active-skeleton variant of
`appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn`. -/
theorem appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn_skeleton
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (Hraw₁ Hraw₂ :
      OmegaPolymerType HF z →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : MeasureTheory.Measure γ)
    (ν : MeasureTheory.Measure β)
    (Y : Finset (Cube d L))
    (hz :
      ∀ X : OmegaPolymerType HF
          (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν),
        skeleton HF X.val ⊆ skeleton HF Y →
          appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν X.val =
            appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₂ μ ν X.val) :
    appendixFHoleHsharpOfIntegratedKsharp HF z Λ Hraw₁ μ ν Y =
      appendixFHoleHsharpOfIntegratedKsharp HF z Λ Hraw₂ μ ν Y := by
  exact appendixFHoleHsharp_eq_of_activity_eq_on_skeleton
    HF
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₁ μ ν)
    (appendixFHoleIntegratedKsharpActivity HF z Λ Hraw₂ μ ν)
    Y hz

end YangMills.RG
