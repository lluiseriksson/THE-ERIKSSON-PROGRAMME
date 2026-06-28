/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229

/-!
# Cammarota-to-CMP116 equation (2.29) source transport

This module isolates the first theorem-fed step in the Cammarota/CMP85 lane for
CMP116 equation (2.29).  The old landing pad `CammarotaCMP85Threshold` carries
the target predicate `CMP116Eq229Summability` directly as a field.  The source
shape below is narrower: a Cammarota/Mayer source theorem supplies a summability
bound for its own finite source product, and a separate dictionary/comparison
lemma identifies the CMP116 `D`-stage product as termwise bounded by that source
product.

The main theorem then proves `CMP116Eq229Summability` by finite-sum domination.
Thus callers using this constructor no longer have to assume the target Eq. (2.29)
summability predicate verbatim.

Honest scope: this file does not extract the primary Cammarota theorem, prove its
smallness constants, or build the Balaban `D`-family dictionary.  It proves the
Lean transport step that turns such a source theorem plus the product comparison
into the existing Eq. (2.29) consumer.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source-side finite `D`-stage summability theorem in the Cammarota/CMP85 lane.

`sourceProduct` is deliberately not forced to be the CMP116 product
`∏_{Y ∈ D} α₆ exp (-δκ d_k(Y))`.  It represents the product/fugacity expression
as it is stated in the external polymer/Mayer theorem after source extraction.
The separate comparison lemma below is the dictionary that transports this source
product to Balaban's Eq. (2.29) product. -/
structure CammarotaCMP85FiniteDStageSource
    {σ ιD : Type*}
    (DIndex : σ → Finset ιD)
    (sourceProduct : σ → ιD → ℝ) : Prop where
  summability :
    ∀ Y0,
      Finset.sum (DIndex Y0) (fun D => sourceProduct Y0 D) ≤ 1

/-- Transport a Cammarota/CMP85 source `D`-stage bound to the exact CMP116
Eq. (2.29) summability predicate.

This is the real finite-sum step: the target `CMP116Eq229Summability` is derived
from a source theorem about `sourceProduct` and a termwise dictionary/comparison,
not assumed as a field. -/
theorem CMP116Eq229Summability.of_cammarotaFiniteDStageSource
    {σ ιD ιY : Type*}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (sourceProduct : σ → ιD → ℝ)
    (S : CammarotaCMP85FiniteDStageSource DIndex sourceProduct)
    (hproduct_le_source :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          sourceProduct Y0 D) :
    CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric := by
  intro Y0
  calc
    Finset.sum (DIndex Y0)
        (fun D =>
          Finset.prod (DParts Y0 D)
            (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) ≤
      Finset.sum (DIndex Y0) (fun D => sourceProduct Y0 D) := by
        exact
          Finset.sum_le_sum (fun D hD => by
            simpa [cmp116Eq229Product] using hproduct_le_source Y0 D hD)
    _ ≤ 1 := S.summability Y0

/-- Build the existing `CammarotaCMP85Threshold` record from a source theorem and
the Balaban/CMP116 product comparison.

Compared with supplying `CammarotaCMP85Threshold` directly, this removes the
direct target-field obligation
`CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric` from callers of
this route.  The remaining source-facing obligations are the extracted theorem
statement, constants, dictionary, and the concrete product comparison. -/
theorem CammarotaCMP85Threshold.of_finiteDStageSource
    {σ ιD ιY : Type*}
    {theoremStatementExtracted : Prop}
    {sourceConstantsMatchCMP116 : Prop}
    {dstageDictionary : Prop}
    {DIndex : σ → Finset ιD}
    {DParts : σ → ιD → Finset ιY}
    {alpha6 delta kappa : ℝ}
    {metric : σ → ιY → ℕ}
    (sourceProduct : σ → ιD → ℝ)
    (hstatement : theoremStatementExtracted)
    (hconstants : sourceConstantsMatchCMP116)
    (hdictionary : dstageDictionary)
    (S : CammarotaCMP85FiniteDStageSource DIndex sourceProduct)
    (hproduct_le_source :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          sourceProduct Y0 D) :
    CammarotaCMP85Threshold
      theoremStatementExtracted sourceConstantsMatchCMP116 dstageDictionary
      DIndex DParts alpha6 delta kappa metric := by
  refine
    { theorem_statement_extracted := hstatement
      source_constants_match_cmp116 := hconstants
      dstage_dictionary := hdictionary
      summability := ?_ }
  exact
    CMP116Eq229Summability.of_cammarotaFiniteDStageSource
      DIndex DParts alpha6 delta kappa metric
      sourceProduct S hproduct_le_source

end YangMills.RG
