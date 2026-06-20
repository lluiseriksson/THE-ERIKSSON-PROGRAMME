/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpGeometricMajorant

/-!
# Appendix F: source-facing absolute majorants for `H#`

This module exposes the finite nonnegative object a future source proof should
estimate for the second-Ursell `H#` layer.  It defines the absolute fixed-union
fiber term and proves that it bounds the complex `appendixFHoleHsharpTerm` by
the triangle inequality.  The remaining declarations package a geometric
source contract and adapt it to the existing geometric `H#` consumers.

No Dimock, Balaban, KP, or Yang-Mills analytic estimate is proved here.  The
fixed-union absolute geometric bound and the closed scalar residual comparison
remain explicit hypotheses.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- The finite nonnegative absolute-value counterpart of
`appendixFHoleHsharpTerm`.  This is the exact fixed-union object a source
tree/KP estimate should bound term by term. -/
noncomputable def appendixFHoleHsharpAbsTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y),
      |((KP.ursell (omegaHolePolymerSystem HF zK) X : ℤ) : ℝ)| *
        ∏ i, ‖(omegaHolePolymerSystem HF zK).activity (X i)‖

/-- The complex fixed-union `H#` term is bounded by its finite absolute
fixed-union counterpart. -/
theorem norm_appendixFHoleHsharpTerm_le_absTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) :
    ‖appendixFHoleHsharpTerm HF zK Y n‖ ≤
      appendixFHoleHsharpAbsTerm HF zK Y n := by
  classical
  rw [appendixFHoleHsharpTerm_eq_sum_filter, appendixFHoleHsharpAbsTerm,
    norm_mul]
  have hfac :
      ‖(((n + 1).factorial : ℂ))⁻¹‖ =
        (((n + 1).factorial : ℝ))⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [show (((n + 1).factorial : ℂ)) =
        (((n + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (by positivity : (0 : ℝ) ≤ ((n + 1).factorial : ℝ))]
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le
    ((Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y))
    (fun X =>
      (KP.ursell (omegaHolePolymerSystem HF zK) X : ℂ) *
        ∏ i, (omegaHolePolymerSystem HF zK).activity (X i))).trans ?_
  refine Finset.sum_le_sum ?_
  intro X _hX
  rw [norm_mul, norm_prod]
  rw [show
      ((KP.ursell (omegaHolePolymerSystem HF zK) X : ℤ) : ℂ) =
        (((KP.ursell (omegaHolePolymerSystem HF zK) X : ℤ) : ℝ) : ℂ) by
        push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- Source-facing geometric majorant contract for the Appendix-F second-Ursell
activity.  The analytic producer supplies the amplitude `A`, ratio `q`, the
termwise bound, and the closed residual comparison; this record only packages
those data for downstream consumers. -/
structure AppendixFHsharpSourceMajorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (C H₀ c₀ κ κ₀ : ℝ) where
  A : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  q : ℕ → ℕ → OmegaPolymerType HF zCarrier → ℝ
  A_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ A t k P
  q_nonneg :
    ∀ t k (P : OmegaPolymerType HF zCarrier), 0 ≤ q t k P
  q_lt_one :
    ∀ t k (P : OmegaPolymerType HF zCarrier), q t k P < 1
  term_le :
    ∀ t k (P : OmegaPolymerType HF zCarrier) n,
      ‖appendixFHoleHsharpTerm HF (zK t k) P.val n‖ ≤
        A t k P * q t k P ^ n
  closed_le_residual :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      A t k P * (1 - q t k P)⁻¹ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))

/-- Construct the source contract from a geometric estimate on the finite
absolute fixed-union term. -/
noncomputable def appendixFHsharpSourceMajorant_of_absTerm_geometric
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
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF (zK t k) P.val n ≤
          A t k P * q t k P ^ n)
    (hclosed :
      ∀ t k (P : OmegaPolymerType HF zCarrier),
        A t k P * (1 - q t k P)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) :
    AppendixFHsharpSourceMajorant
      HF zCarrier zK g C H₀ c₀ κ κ₀ := by
  refine
    { A := A
      q := q
      A_nonneg := hA
      q_nonneg := hq0
      q_lt_one := hq1
      term_le := ?_
      closed_le_residual := hclosed }
  intro t k P n
  exact
    (norm_appendixFHoleHsharpTerm_le_absTerm
      HF (zK t k) P.val n).trans
      (habs t k P n)

namespace AppendixFHsharpSourceMajorant

variable
    {HF : HoleFamily d L}
    {zCarrier : Finset (Cube d L) → ℂ}
    {zK : ℕ → ℕ → Finset (Cube d L) → ℂ}
    {g : ℕ → ℝ}
    {C H₀ c₀ κ κ₀ : ℝ}

/-- A source majorant supplies fixed-target summability of the `H#`
cluster-size terms. -/
theorem summable_terms
    (hsrc :
      AppendixFHsharpSourceMajorant
        HF zCarrier zK g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    Summable (fun n : ℕ =>
      appendixFHoleHsharpTerm HF (zK t k) P.val n) := by
  exact summable_appendixFHoleHsharpTerm_of_norm_le_majorant
    HF (zK t k) P.val
    (fun n : ℕ => hsrc.A t k P * hsrc.q t k P ^ n)
    (summable_geometric_majorant
      (hsrc.q_nonneg t k P) (hsrc.q_lt_one t k P))
    (hsrc.term_le t k P)

/-- A source majorant supplies the closed shifted-tail error estimate for
finite `H#` truncations. -/
theorem tail_bound
    (hsrc :
      AppendixFHsharpSourceMajorant
        HF zCarrier zK g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier)
    (N : ℕ) :
    ‖appendixFHoleHsharp HF (zK t k) P.val -
        appendixFHoleHsharpPartial HF (zK t k) N P.val‖ ≤
      hsrc.A t k P * hsrc.q t k P ^ N *
        (1 - hsrc.q t k P)⁻¹ := by
  exact norm_appendixFHoleHsharp_sub_partial_le_geometric_tail
    HF (zK t k) P.val N
    (hsrc.q_nonneg t k P)
    (hsrc.q_lt_one t k P)
    (hsrc.term_le t k P)

/-- A source majorant supplies the pointwise total residual estimate for
`H#`. -/
theorem residual_bound
    (hsrc :
      AppendixFHsharpSourceMajorant
        HF zCarrier zK g C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  exact norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
    HF zCarrier zK g hsrc.A hsrc.q
    hsrc.A_nonneg hsrc.q_nonneg hsrc.q_lt_one
    hsrc.term_le hsrc.closed_le_residual

end AppendixFHsharpSourceMajorant

/-- A factorized constructor for the preferred source shape: target geometry is
isolated in the modified-metric exponential, while the cluster-order decay is
carried by a ratio `ρ t k` independent of the target polymer. -/
noncomputable def appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    (B ρ : ℕ → ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hB0 : ∀ t k, 0 ≤ B t k)
    (hρ0 : ∀ t k, 0 ≤ ρ t k)
    (hρ1 : ∀ t k, ρ t k < 1)
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF (zK t k) P.val n ≤
          (B t k *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            ρ t k ^ n)
    (hBclosed :
      ∀ t k,
        B t k * (1 - ρ t k)⁻¹ ≤
          C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) :
    AppendixFHsharpSourceMajorant
      HF zCarrier zK g C H₀ c₀ κ κ₀ := by
  refine appendixFHsharpSourceMajorant_of_absTerm_geometric
    HF zCarrier zK g
    (fun t k P =>
      B t k *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    (fun t k _P => ρ t k)
    ?_ ?_ ?_ habs ?_
  · intro t k P
    exact mul_nonneg (hB0 t k) (Real.exp_nonneg _)
  · intro t k P
    exact hρ0 t k
  · intro t k P
    exact hρ1 t k
  · intro t k P
    calc
      (B t k *
              Real.exp
                (-(polymerClusterResidualRate κ κ₀ *
                  ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
            (1 - ρ t k)⁻¹
          =
        (B t k * (1 - ρ t k)⁻¹) *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
          ring
      _ ≤
        (C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀) *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (hBclosed t k) (Real.exp_nonneg _)
      _ =
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
          ring

/-! ## Integrated `K#` source specialization -/

/-- Scale-indexed family of spectator-integrated scalar first activities.
This is just a named `zK t k` carrier for the concrete normalization
`z_K(Y) = ∫ K#(Y, ψ) dν(ψ)`; it does not include any quantitative estimate. -/
noncomputable def appendixFHoleIntegratedKsharpActivityFamily
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (t k : ℕ)
    (Y : Finset (Cube d L)) : ℂ :=
  appendixFHoleIntegratedKsharpActivity
    HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k) Y

@[simp] theorem appendixFHoleIntegratedKsharpActivityFamily_eq
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (t k : ℕ)
    (Y : Finset (Cube d L)) :
    appendixFHoleIntegratedKsharpActivityFamily
      HF z Λ Hraw μ ν t k Y =
      appendixFHoleIntegratedKsharpActivity
        HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k) Y := rfl

/-- Integrated-`K#` specialization of the absolute-term geometric source
majorant constructor.  A source proof still supplies the finite fixed-union
absolute estimate and the closed residual comparison explicitly. -/
noncomputable def
    appendixFHsharpSourceMajorant_of_integratedKsharp_absTerm_geometric
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
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF
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
  appendixFHsharpSourceMajorant_of_absTerm_geometric
    HF zCarrier
    (fun t k Y =>
      appendixFHoleIntegratedKsharpActivityFamily
        HF z Λ Hraw μ ν t k Y)
    g A q hA hq0 hq1 habs hclosed

/-- Factorized integrated-`K#` source-majorant constructor, isolating target
geometry in the modified-metric exponential and leaving the source proof to
supply only the finite tree/absolute estimate and closed amplitude bound. -/
noncomputable def
    appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_absTerm_geometric
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
    (habs :
      ∀ t k (P : OmegaPolymerType HF zCarrier) n,
        appendixFHoleHsharpAbsTerm HF
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
  appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
    HF zCarrier
    (fun t k Y =>
      appendixFHoleIntegratedKsharpActivityFamily
        HF z Λ Hraw μ ν t k Y)
    g B ρ hB0 hρ0 hρ1 habs hBclosed

/-- Residual estimate rewritten for the named integrated `H#` object. -/
theorem norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_source_majorant
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
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant HF zCarrier
        (fun t k Y =>
          appendixFHoleIntegratedKsharpActivityFamily
            HF z Λ Hraw μ ν t k Y)
        g C H₀ c₀ κ κ₀)
    (t k : ℕ)
    (P : OmegaPolymerType HF zCarrier) :
    ‖appendixFHoleHsharpOfIntegratedKsharp
        HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  change
    ‖appendixFHoleHsharp HF
        (appendixFHoleIntegratedKsharpActivity
          HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k)) P.val‖ ≤
      C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
        Real.exp
          (-(polymerClusterResidualRate κ κ₀ *
            ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))
  exact
    norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
      HF zCarrier
      (fun t k Y =>
        appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k Y)
      g hsrc.A hsrc.q hsrc.A_nonneg hsrc.q_nonneg hsrc.q_lt_one
      hsrc.term_le hsrc.closed_le_residual t k P

/-- The source contract feeds directly into the existing closed-form geometric
total residual consumer. -/
theorem norm_appendixFHoleHsharp_le_residual_of_source_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant
        HF zCarrier zK g C H₀ c₀ κ κ₀) :
    ∀ t k (P : OmegaPolymerType HF zCarrier),
      ‖appendixFHoleHsharp HF (zK t k) P.val‖ ≤
        C * H₀ * Real.exp (-(c₀ * (t : ℝ))) * g k ^ κ₀ *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) := by
  exact
    norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
      HF zCarrier zK g hsrc.A hsrc.q
      hsrc.A_nonneg hsrc.q_nonneg hsrc.q_lt_one
      hsrc.term_le hsrc.closed_le_residual

/-- Real-part omega-rooted UV consumer fed by the packaged source majorant and
the sufficient residual margin `κ ≥ 4κ₀ + 3`. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (zK : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant
        HF zCarrier zK g C H₀ c₀ κ κ₀)
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (appendixFHoleHsharp HF (zK t k) P.val.val))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  exact
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_geometric_term_majorant
      HF zCarrier r zK Rsc g hsrc.A hsrc.q
      hC hH₀ hg hκ hR
      hsrc.A_nonneg hsrc.q_nonneg hsrc.q_lt_one
      hsrc.term_le hsrc.closed_le_residual
      hdisj hnoedges hholes_ne hCq

/-- Real-part omega-rooted UV consumer for the integrated `H#` normal form.
The source majorant remains an explicit hypothesis; this theorem only performs
the specialization from the abstract `zK` family to the spectator-integrated
first activity. -/
theorem
    singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (HF : HoleFamily d L)
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (Hraw : ∀ t k,
      OmegaPolymerType HF (z t k) →
        LocalActivity (Cube d L) (fun _ => β) (fun _ => γ) ℂ)
    (μ : ℕ → ℕ → MeasureTheory.Measure γ)
    (ν : ℕ → ℕ → MeasureTheory.Measure β)
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    {C H₀ c₀ κ κ₀ : ℝ}
    (hsrc :
      AppendixFHsharpSourceMajorant HF zCarrier
        (fun t k Y =>
          appendixFHoleIntegratedKsharpActivityFamily
            HF z Λ Hraw μ ν t k Y)
        g C H₀ c₀ κ κ₀)
    (hC : 0 ≤ C)
    (hH₀ : 0 ≤ H₀)
    (hg : ∀ k, 0 ≤ g k)
    (hκ : 4 * κ₀ + 3 ≤ κ)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (appendixFHoleHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k) (Hraw t k)
                (μ t k) (ν t k) P.val.val))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne :
      ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    SingleScaleUVDecay Rsc g
      ((C * H₀) *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)))⁻¹)
      c₀ κ₀ := by
  refine
    singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
      HF zCarrier r
      (fun t k Y =>
        appendixFHoleIntegratedKsharpActivityFamily
          HF z Λ Hraw μ ν t k Y)
      Rsc g hsrc hC hH₀ hg hκ ?_
      hdisj hnoedges hholes_ne hCq
  intro t k
  change
    Rsc t k =
      ∑' P : { P : OmegaPolymerType HF zCarrier //
          r ∈ skeleton HF P.val },
        Complex.re
          (appendixFHoleHsharp HF
            (appendixFHoleIntegratedKsharpActivity
              HF (z t k) (Λ t k) (Hraw t k) (μ t k) (ν t k))
            P.val.val)
  exact hR t k

end YangMills.RG
