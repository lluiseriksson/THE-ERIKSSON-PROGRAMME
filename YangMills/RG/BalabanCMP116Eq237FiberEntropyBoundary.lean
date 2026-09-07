/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger
import YangMills.RG.BalabanCMP116Eq237

/-!
# The genuine fiber-entropy boundary in CMP116 equation (2.37)

The fixed-`Z0'` estimate has two logically different inputs.  First, each
literal equation-(2.26) term must be compared with its domain, `P`, gap, and
Gaussian-volume ledger.  Second, the number of compatible `Z0` choices must
be absorbed by the product over connected components printed in equation
(2.37).

This module separates those inputs.  In particular, the remaining entropy
premise contains neither `termWeight` nor an already resummed bound.
-/

namespace YangMills.RG

noncomputable section

/-- The connected-component product in the middle of the fixed-`Z0'`
equation-(2.37) weight. -/
def cmp116Eq237ComponentProduct
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (C237 : ℝ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (Z : σ) (Z0' : ιZ0') : ℝ :=
  Finset.prod (components Z Z0') (fun Zi =>
    cmp116Eq237Amplitude hp.blockScale C237 hp.epsilon2 *
      Real.exp
        (-(((1 - 7 * hp.delta) / 2) *
          (hp.blockScale : ℝ) * hp.kappa *
            (componentMetric Z Z0' Zi : ℝ))))

/-- Exact source-ledger factorization of the fixed-`Z0'` weight into gap,
component entropy, and Gaussian-volume factors. -/
theorem cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian
    {σ ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (Z : σ) (Z0' : ιZ0') :
    cmp116Eq237FixedZ0PrimeWeight
        hp localizationScale C237 Calpha5 alpha5
        sourceCard gapCard components componentMetric Z Z0' =
      cmp116Eq226GapFactor
          hp.kappa1 localizationScale 1 (gapCard Z Z0') *
        cmp116Eq237ComponentProduct
          hp C237 components componentMetric Z Z0' *
        cmp116Eq226GaussianVolumeFactor
          Calpha5 alpha5 (sourceCard Z) := by
  unfold cmp116Eq237FixedZ0PrimeWeight cmp116Eq226GapFactor
    cmp116Eq237ComponentProduct cmp116Eq226GaussianVolumeFactor
  norm_num

/-- A pointwise literal-ledger comparison and the pure cardinal entropy
bound imply the raw fixed-`Z0'` estimate.  The second premise is the genuine
finite combinatorial content of equation (2.37). -/
theorem cmp116Eq237_rawFixed_of_pointwiseLedger_and_fiberEntropy
    {ιZ0 : Type*}
    (fiber : Finset ιZ0)
    (termWeight : ιZ0 → ℝ)
    (domainPWeight gapWeight gaussianWeight componentProduct : ℝ)
    (hbase_nonneg :
      0 ≤ domainPWeight * gapWeight * gaussianWeight)
    (hpointwise :
      ∀ Z0 ∈ fiber,
        termWeight Z0 ≤
          domainPWeight * gapWeight * gaussianWeight)
    (hfiberEntropy :
      (fiber.card : ℝ) ≤ componentProduct) :
    Finset.sum fiber termWeight ≤
      domainPWeight * gapWeight * componentProduct * gaussianWeight := by
  have hsum :
      Finset.sum fiber termWeight ≤
        (fiber.card : ℝ) *
          (domainPWeight * gapWeight * gaussianWeight) := by
    calc
      Finset.sum fiber termWeight ≤
          Finset.sum fiber (fun _ =>
            domainPWeight * gapWeight * gaussianWeight) :=
        Finset.sum_le_sum hpointwise
      _ =
          (fiber.card : ℝ) *
            (domainPWeight * gapWeight * gaussianWeight) := by
        simp
  calc
    Finset.sum fiber termWeight ≤
        (fiber.card : ℝ) *
          (domainPWeight * gapWeight * gaussianWeight) := hsum
    _ ≤
        componentProduct *
          (domainPWeight * gapWeight * gaussianWeight) :=
      mul_le_mul_of_nonneg_right hfiberEntropy hbase_nonneg
    _ =
        domainPWeight * gapWeight * componentProduct * gaussianWeight := by
      ring

/-- Source-shaped specialization: the only non-pointwise premise is the
cardinality estimate by the literal component product of equation (2.37). -/
theorem cmp116Eq237_rawFixed_of_sourcePointwiseLedger_and_fiberEntropy
    {σ ιZ0 ιZ0' ιC : Type*}
    (hp : CMP116Lemma3Parameters)
    (localizationScale : ℕ)
    (C237 Calpha5 alpha5 : ℝ)
    (sourceCard : σ → ℕ)
    (gapCard : σ → ιZ0' → ℕ)
    (components : σ → ιZ0' → Finset ιC)
    (componentMetric : σ → ιZ0' → ιC → ℕ)
    (Z : σ) (Z0' : ιZ0')
    (fiber : Finset ιZ0)
    (termWeight : ιZ0 → ℝ)
    (domainPWeight : ℝ)
    (hbase_nonneg :
      0 ≤
        domainPWeight *
          cmp116Eq226GapFactor
            hp.kappa1 localizationScale 1 (gapCard Z Z0') *
          cmp116Eq226GaussianVolumeFactor
            Calpha5 alpha5 (sourceCard Z))
    (hpointwise :
      ∀ Z0 ∈ fiber,
        termWeight Z0 ≤
          domainPWeight *
            cmp116Eq226GapFactor
              hp.kappa1 localizationScale 1 (gapCard Z Z0') *
            cmp116Eq226GaussianVolumeFactor
              Calpha5 alpha5 (sourceCard Z))
    (hfiberEntropy :
      (fiber.card : ℝ) ≤
        cmp116Eq237ComponentProduct
          hp C237 components componentMetric Z Z0') :
    Finset.sum fiber termWeight ≤
      domainPWeight *
        cmp116Eq237FixedZ0PrimeWeight
          hp localizationScale C237 Calpha5 alpha5
          sourceCard gapCard components componentMetric Z Z0' := by
  rw [
    cmp116Eq237FixedZ0PrimeWeight_eq_gap_mul_componentProduct_mul_gaussian]
  simpa [mul_assoc] using
    cmp116Eq237_rawFixed_of_pointwiseLedger_and_fiberEntropy
      fiber termWeight domainPWeight
      (cmp116Eq226GapFactor
        hp.kappa1 localizationScale 1 (gapCard Z Z0'))
      (cmp116Eq226GaussianVolumeFactor
        Calpha5 alpha5 (sourceCard Z))
      (cmp116Eq237ComponentProduct
        hp C237 components componentMetric Z Z0')
      hbase_nonneg hpointwise hfiberEntropy

end

end YangMills.RG
