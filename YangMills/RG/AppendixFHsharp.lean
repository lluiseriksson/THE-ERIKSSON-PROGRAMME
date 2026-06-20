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

end YangMills.RG
