/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpSourceMajorant
import YangMills.KP.KPBound

/-!
# Appendix F: finite source-facing tree majorants for the second Ursell layer

This module adds the first source-independent coefficientwise step behind the
Appendix-F `H#` estimate: the exact fixed-union absolute term is dominated by
the corresponding finite sum over spanning trees of the incompatibility graph.

This is only Penrose tree-graph bookkeeping for a finite fiber.  It does not
prove Dimock's leaf summation, the pointwise `K#` estimate (642)/(644), the
source `H#` estimate F.1/(636), any smallness condition, or any Yang--Mills
raw activity bound.  The constructors at the bottom of the file only turn a
future tree-term estimate into the existing source-majorant contract.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- The finite tree-graph majorant for the fixed-union `H#` coefficient.  It
has the same target fiber and factorial normalization as
`appendixFHoleHsharpAbsTerm`, but replaces the absolute Ursell coefficient by
the number of spanning trees of the tuple incompatibility graph. -/
noncomputable def appendixFHoleHsharpTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y),
      ∑ _T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        ∏ i, ‖(omegaHolePolymerSystem HF zK).activity (X i)‖

/-- Penrose tree-graph domination for the exact finite fixed-union
second-Ursell coefficient. -/
theorem appendixFHoleHsharpAbsTerm_le_treeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) :
    appendixFHoleHsharpAbsTerm HF zK Y n ≤
      appendixFHoleHsharpTreeTerm HF zK Y n := by
  classical
  unfold appendixFHoleHsharpAbsTerm appendixFHoleHsharpTreeTerm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro X _hX
  let P := omegaHolePolymerSystem HF zK
  let trees := KP.spanningTrees (KP.incompGraph P X)
  let weight : ℝ := ∏ i, ‖P.activity (X i)‖
  have hweight_nonneg : 0 ≤ weight := by
    exact Finset.prod_nonneg fun i _ => norm_nonneg _
  have hU := KP.abs_ursell_le_card_spanningTrees P X
  have hUreal :
      |((KP.ursell P X : ℤ) : ℝ)| ≤ (trees.card : ℝ) := by
    exact_mod_cast hU
  calc
    |((KP.ursell P X : ℤ) : ℝ)| * weight
        ≤ (trees.card : ℝ) * weight :=
          mul_le_mul_of_nonneg_right hUreal hweight_nonneg
    _ =
        ∑ _T ∈ trees, weight := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- Construct a source majorant from a geometric estimate on the finite
tree-term majorant.  This is the precise finite bridge from Penrose
tree-graph bookkeeping to the already-packaged source contract. -/
noncomputable def appendixFHsharpSourceMajorant_of_treeTerm_geometric
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF (zK t k) P.val n ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpSourceMajorant HF zCarrier zK g C H₀ c₀ κ κ₀ :=
  appendixFHsharpSourceMajorant_of_absTerm_geometric
    HF zCarrier zK g A q hA hq0 hq1
    (fun t k P n =>
      (appendixFHoleHsharpAbsTerm_le_treeTerm
        HF (zK t k) P.val n).trans
        (htree t k P n))
    hclosed

/-- Factorized constructor from a finite tree-term estimate.  The remaining
source obligation is now exactly the target-sensitive tree bound with the
modified-metric exponential and the cluster-order ratio. -/
noncomputable def appendixFHsharpSourceMajorant_of_factorized_treeTerm_geometric
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (B ρ : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hB0 : ∀ t k, 0 ≤ B t k)
    (hρ0 : ∀ t k, 0 ≤ ρ t k)
    (hρ1 : ∀ t k, ρ t k < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF (zK t k) P.val n ≤
          (B t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            ρ t k ^ n)
    (hBclosed :
      ∀ t k,
        B t k * (1 - ρ t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpSourceMajorant HF zCarrier zK g C H₀ c₀ κ κ₀ :=
  appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
    HF zCarrier zK g B ρ hB0 hρ0 hρ1
    (fun t k P n =>
      (appendixFHoleHsharpAbsTerm_le_treeTerm
        HF (zK t k) P.val n).trans
        (htree t k P n))
    hBclosed

/-- Integrated-`K#` specialization of the tree-term source-majorant
constructor.  This moves the source obligation from the abstract absolute
term to the finite Penrose tree term for the concrete integrated first
activity. -/
noncomputable def
    appendixFHsharpSourceMajorant_of_integratedKsharp_treeTerm_geometric
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (g : ℕ → ℝ)
    (A q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hA :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P)
    (hq0 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P)
    (hq1 :
      ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF
            (appendixFHoleIntegratedKsharpActivityFamily
              HF z Λ Hraw μ ν t k) P.val n ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  appendixFHsharpSourceMajorant_of_integratedKsharp_absTerm_geometric
    HF zCarrier z Λ Hraw μ ν g A q hA hq0 hq1
    (fun t k P n =>
      (appendixFHoleHsharpAbsTerm_le_treeTerm HF
        (appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k) P.val n).trans
        (htree t k P n))
    hclosed

/-- Factorized integrated-`K#` constructor from a finite tree-term estimate.
This is the source-facing normal form expected before the analytic
Balaban/Dimock leaf summation is supplied. -/
noncomputable def
    appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_treeTerm_geometric
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (g : ℕ → ℝ)
    (B ρ : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hB0 : ∀ t k, 0 ≤ B t k)
    (hρ0 : ∀ t k, 0 ≤ ρ t k)
    (hρ1 : ∀ t k, ρ t k < 1)
    (htree :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpTreeTerm HF
            (appendixFHoleIntegratedKsharpActivityFamily
              HF z Λ Hraw μ ν t k) P.val n ≤
          (B t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            ρ t k ^ n)
    (hBclosed :
      ∀ t k,
        B t k * (1 - ρ t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpSourceMajorant HF zCarrier
      (fun t k Y =>
        appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k Y)
      g C H₀ c₀ κ κ₀ :=
  appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_absTerm_geometric
    HF zCarrier z Λ Hraw μ ν g B ρ hB0 hρ0 hρ1
    (fun t k P n =>
      (appendixFHoleHsharpAbsTerm_le_treeTerm HF
        (appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k) P.val n).trans
        (htree t k P n))
    hBclosed

end YangMills.RG
