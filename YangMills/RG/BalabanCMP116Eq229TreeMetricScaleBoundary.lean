/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq230TreeMetric
import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# Source-tree equation-(2.29) scale boundary

This module inserts the constructed four-dimensional cube-edge tree metric
into the scale-family boundary consumed by the literal equation-(2.26) and
Lemma-3 pipeline.

The only dictionary inputs identify, for each fixed source context `Z`,

* its nonempty fixed union `Y₀`;
* the physical `DIndex Z` with the exact-union fiber over `Y₀`; and
* `DParts Z D` with the family `D` itself.

All analytic content of equation (2.29), including equation (2.27), the
shifted cardinal comparison, connected-domain entropy, and the metric itself,
is then generated internally.
-/

namespace YangMills.RG

open Finset

/-- Construct the full scale-family equation-(2.29) boundary from the
source-tree metric and an exact-union dictionary.

No `CMP116Eq229Summability`, equation-(2.27), or metric-cardinality estimate
is supplied by the caller. -/
theorem CMP116Lemma3Eq229ScaleBoundary.of_sourceTreeMetric_exactUnion
    {σ ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc N' : ℕ} [NeZero N] [NeZero N']
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k)
          (Finset (Finset (FinBox 4 N')))
          (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts :
      ∀ t k, σ t k →
        Finset (Finset (FinBox 4 N')) →
          Finset (Finset (FinBox 4 N')))
    (domainFamily :
      ∀ _t _k, Finset (Finset (FinBox 4 N')))
    (unionOf :
      ∀ t k, σ t k → Finset (FinBox 4 N'))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (hDIndex :
      ∀ t k Z,
        (R t k).DIndex Z =
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hDParts :
      ∀ _t _k Z D, DParts _t _k Z D = D)
    (alpha6 : ℕ → ℕ → ℝ)
    (halpha6 : ∀ t k, 0 ≤ alpha6 t k)
    (hdeltaKappa :
      ∀ t k, 0 ≤ (hp t k).delta * (hp t k).kappa)
    (hCq :
      ∀ t k,
        64 *
          Real.exp
            (-(((hp t k).delta * (hp t k).kappa) / 48)) < 1)
    (huniform :
      ∀ t k,
        (alpha6 t k *
            Real.exp
              (3 * ((hp t k).delta * (hp t k).kappa))) *
            24 *
            (1 -
              64 *
                Real.exp
                  (-(((hp t k).delta * (hp t k).kappa) / 48)))⁻¹ ≤
          ((hp t k).delta * (hp t k).kappa) / 2) :
    CMP116Lemma3Eq229ScaleBoundary hp R DParts alpha6
      (fun _t _k _Z Y => cmp116SourceTreeMetric Y) := by
  refine ⟨?_, halpha6⟩
  intro t k Z
  have hsummable :=
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230Shifted_uniform
      (domainFamily t k)
      (unionOf t k Z)
      (hunion_nonempty t k Z)
      (hdomains t k)
      (alpha6 t k)
      (hp t k).delta
      (hp t k).kappa
      cmp116SourceTreeMetric
      (halpha6 t k)
      (hdeltaKappa t k)
      (fun Y hY =>
        cmp116SourceTreeMetric_eq230_shifted
          Y (hdomains t k Y hY).1 (hdomains t k Y hY).2)
      (hCq t k)
      (huniform t k)
  rw [hDIndex t k Z]
  simpa [hDParts] using hsummable

end YangMills.RG
