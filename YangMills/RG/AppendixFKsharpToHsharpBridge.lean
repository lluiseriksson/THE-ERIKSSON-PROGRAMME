/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson (proposal draft)

This is a STANDALONE PROPOSAL file, not yet wired into `YangMillsCore`.
It compiles against the current verified core (`lake build
YangMills.RG.AppendixFKsharpToHsharpBridge`).  Oracle target:
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, no axioms.
-/

import YangMills.RG.AppendixFKsharpEstimate
import YangMills.RG.AppendixFHsharpSourceResidual
import YangMills.RG.AppendixFSecondUrsellGeometry

/-!
# Proposal: the `K# → H#` source bridge (discharges `hactivityKsharp`)

The all-tail residual `H#` theorem
`norm_appendixFHoleHsharp_le_residual_of_dimockII_appendixF_sourceEstimate`
(`AppendixFHsharpSourceResidual.lean`) reduces the second-Ursell `H#`
activity decay to **three** source-facing hypotheses:

* `hactivityKsharp : ‖zK t k Q‖ ≤ epsilon t k *
    appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val`,
* `hsmall          : appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1`,
* `hbudget         : (momentConst * eps) * (1 - leafConst * eps)⁻¹ ≤
    C * H₀ * exp(-c₀ t) * g k ^ κ₀`.

The first-gas `K#` activity estimate at the same rate is **already proved**
in `AppendixFKsharpEstimate.lean`:
`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`,
giving
    ‖K#(Y, ψ)‖ ≤ (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y.

This file closes the formal gap between that proved `K#` estimate and the
`hactivityKsharp` obligation of the residual `H#` theorem, when the
second-gas carrier `zK t k` is the integrated first activity
`K#(·, ψ)` and the scalar prefactor is `ε_val = 2 * H₀ * K₀`.

## What this proposal proves (faithful, oracle-clean)

* **`ksharp_hactivityKsharp`** — given the already-verified rooted `K#`
  bound, the pointwise activity hypothesis `hactivityKsharp` holds with
  `epsilon t k := ε_val`.  The carrier `zK t k` is the integrated `K#`
  activity evaluated at `ψ`.

## What this proposal does NOT prove (honest scope)

* It does **not** prove the analytic first-activity estimate
  `norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`
  itself (that is the banked theorem); it only consumes it.
* It does **not** discharge the smallness `hsmall` or the closed scalar
  budget `hbudget` from the Yang–Mills activity — those remain the genuine
  analytic content of P4 / Dimock II §3.14.  This proposal makes the
  prefactor `ε_val = 2 * H₀ * K₀` explicit, which is the form P4 must
  eventually bound.
* It does **not** close `hRpoly`, M3, or any Clay obstruction.  Distance to
  the Clay prize **~0% (<0.1%), unchanged**.

**Source.** Dimock II (arXiv:1212.5562) Appendix F, Theorem F.1 (the
`H#`-decay `|H#(Y)| ≤ O(1)·H₀·exp(-(κ-3κ₀-3)·d_M(Y, mod Ωᶜ))`); the
first-gas `K#` estimate is Dimock II eq. (642)/Lemma 3.18.  The constants
`appendixFSecondUrsellLeafConstant`, `appendixFSecondUrsellMomentConstant`
are the repo's faithful realizations of the Appendix-F leaf/moment constants.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open Finset
open scoped BigOperators

/-- The canonical scalar prefactor `ε_val = 2 * H₀ * K₀` produced by the
rooted first-gas `K#` estimate
(`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`).
This is the value of `epsilon t k` that `ksharp_hactivityKsharp` feeds into
the source estimate, and the scalar whose smallness (`< 1 / leafConst`) P4
must eventually prove from the Yang–Mills activity. -/
noncomputable def ksharpEpsilonVal (H₀ K₀ : ℝ) : ℝ := 2 * H₀ * K₀

/-- **`hactivityKsharp` from the banked rooted `K#` estimate.**  Given the
already-proved rooted first-gas `K#` bound
`norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted`,
the pointwise activity obligation `hactivityKsharp` of
`dimockII_appendixF_weightedTree_sourceEstimate` holds with the uniform
scalar prefactor `epsilon t k := ksharpEpsilonVal H₀ K₀ = 2 * H₀ * K₀`.

The carrier `zK t k` is taken to be the integrated first activity
`(appendixFHoleKsharp HF zCarrier Λ H μ ·).globalEval ψ`; the smallness
condition `2 * H₀ * K₀ ≤ 1` is exactly the rooted estimate's convexity
hypothesis.  This composes the banked `K#` estimate with the source
obligation, leaving only the smallness/budget on the scalar prefactor
(which is P4). -/
theorem ksharp_hactivityKsharp
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF zCarrier))
    (H : OmegaPolymerType HF zCarrier → LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1) (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤ H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : ∀ (t _k : ℕ) (Q : OmegaPolymerType HF zCarrier),
      Q.val ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF zCarrier => skeleton HF X.val)
        (fun X : OmegaPolymerType HF zCarrier => X.val)
        Λ →
      Integrable
        (fun φ =>
          (appendixFHoleConnectedLocalActivity HF zCarrier Λ H Q.val).globalEval ψ φ)
        (Measure.pi fun _ : Cube d L => μ))
    (t k : ℕ) (Q : OmegaPolymerType HF zCarrier)
    (hQregion : Q.val ∈ appendixFTargetRegion
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF zCarrier => skeleton HF X.val)
        (fun X : OmegaPolymerType HF zCarrier => X.val)
        Λ) :
    ‖(appendixFHoleKsharp HF zCarrier Λ H μ Q.val).globalEval ψ‖ ≤
      ksharpEpsilonVal H₀ K₀ *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Q.val := by
  have hkey := norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
    HF zCarrier Λ H μ hQregion ψ hH₀ hH₀_one hK₀ hsmall hκ₀ hκ hroot hraw
    (hint t k Q hQregion)
  simpa [ksharpEpsilonVal] using hkey

/-! ## 2. The scalar `hsmall` and `hbudget` obligations, made explicit.

The residual `H#` theorem's two remaining source obligations `hsmall` and
`hbudget` (beyond `hactivityKsharp`) are, after instantiating
`epsilon t k := ksharpEpsilonVal H₀ K₀`, **scalar** inequalities in the
prefactor `ε_val = 2 * H₀ * K₀`.  These two theorems record them in that
explicit form, so the analytic content of P4 is isolated as a single scalar
smallness/budget condition on `ε_val`.
-/

/-- The `hsmall` obligation reduced to its scalar form: with
`epsilon t k := ksharpEpsilonVal H₀ K₀`, the smallness
`appendixFSecondUrsellLeafConstant d κ₀ * epsilon t k < 1` is exactly

    appendixFSecondUrsellLeafConstant d κ₀ * (2 * H₀ * K₀) < 1.

This is the **sole remaining analytic smallness** once `hactivityKsharp` is
discharged by the banked `K#` estimate.  It is a condition on the raw
activity prefactor `2 * H₀ * K₀`, which P4 (Dimock II §3.14) must prove from
the Yang–Mills fluctuation integral. -/
theorem ksharp_smallness_scalar (d : ℕ) (κ₀ : ℝ) (H₀ K₀ : ℝ) :
    appendixFSecondUrsellLeafConstant d κ₀ * ksharpEpsilonVal H₀ K₀ < 1 ↔
      appendixFSecondUrsellLeafConstant d κ₀ * (2 * H₀ * K₀) < 1 := by
  rfl

/-- The `hbudget` obligation reduced to its scalar form.  With
`epsilon t k := ksharpEpsilonVal H₀ K₀`, the closed scalar budget

    (appendixFSecondUrsellMomentConstant d κ₀ * (2 * H₀ * K₀)) *
        (1 - appendixFSecondUrsellLeafConstant d κ₀ * (2 * H₀ * K₀))⁻¹
      ≤ C * H₀ * exp(-c₀ * t) * g k ^ κ₀

is the **sole remaining analytic budget** once `hactivityKsharp` is
discharged.  P4 (Dimock II §3.14) must bound the left-hand side by the
coupling decay `C * H₀ * exp(-c₀ t) * g^κ₀`. -/
theorem ksharp_budget_scalar (d : ℕ) (κ₀ C H₀ c₀ : ℝ) (t k : ℕ) (g : ℕ → ℝ) :
    (appendixFSecondUrsellMomentConstant d κ₀ * ksharpEpsilonVal H₀ K₀) *
        (1 - appendixFSecondUrsellLeafConstant d κ₀ *
          ksharpEpsilonVal H₀ K₀)⁻¹ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ ↔
    (appendixFSecondUrsellMomentConstant d κ₀ * (2 * H₀ * K₀)) *
        (1 - appendixFSecondUrsellLeafConstant d κ₀ *
          (2 * H₀ * K₀))⁻¹ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ := by
  rfl

end YangMills.RG
