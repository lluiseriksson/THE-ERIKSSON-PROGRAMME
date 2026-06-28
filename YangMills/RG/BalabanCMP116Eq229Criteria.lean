/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229

/-!
# CMP116 equation (2.29): finite majorant criteria

This module removes one use of the raw Eq. (2.29) summability hypothesis.
Instead of asking directly for

`CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric`,

it proves that predicate from explicit finite data: a pointwise majorant for
each fixed-`D` product and a finite sum bound for those majorants.  The uniform
cardinality corollary is the common quick-discharge form.

Honest scope: this is not a primary-source extraction of Cammarota/CMP85.  It is
a formal finite criterion that lets callers replace the global Eq. (2.29)
landing pad by concrete product/cardinality estimates.
-/

namespace YangMills.RG

open scoped BigOperators

/-- CMP116 Eq. (2.29) follows from any finite `D`-indexed product majorant whose
sum is at most one.

This is the local mathematical discharge of the global summability predicate:
callers no longer need to assume `CMP116Eq229Summability` when they can prove a
termwise product bound and the corresponding finite majorant sum. -/
theorem cmp116Eq229Summability_of_product_majorant
    {σ ιD ιY : Type*}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (majorant : σ → ιD → ℝ)
    (hprod :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          majorant Y0 D)
    (hmajorant :
      ∀ Y0, Finset.sum (DIndex Y0) (fun D => majorant Y0 D) ≤ 1) :
    CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric := by
  intro Y0
  calc
    Finset.sum (DIndex Y0)
        (fun D =>
          Finset.prod (DParts Y0 D)
            (cmp116Eq229Weight alpha6 delta kappa (metric Y0))) ≤
      Finset.sum (DIndex Y0) (fun D => majorant Y0 D) := by
        exact Finset.sum_le_sum fun D hD => by
          simpa [cmp116Eq229Product] using hprod Y0 D hD
    _ ≤ 1 := hmajorant Y0

/-- Uniform finite-cardinality discharge of CMP116 Eq. (2.29).

For each fixed source component `Y0`, it is enough to bound every `D`-product by
one scalar `bound Y0` and then prove
`|DIndex Y0| * bound Y0 <= 1`. -/
theorem cmp116Eq229Summability_of_uniform_product_bound
    {σ ιD ιY : Type*}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (bound : σ → ℝ)
    (hprod :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          bound Y0)
    (hcard :
      ∀ Y0, ((DIndex Y0).card : ℝ) * bound Y0 ≤ 1) :
    CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric :=
  cmp116Eq229Summability_of_product_majorant
    DIndex DParts alpha6 delta kappa metric
    (fun Y0 _D => bound Y0)
    hprod
    (by
      intro Y0
      calc
        Finset.sum (DIndex Y0) (fun _D => bound Y0) =
            ((DIndex Y0).card : ℝ) * bound Y0 := by
              simp
        _ ≤ 1 := hcard Y0)

/-- Cammarota/CMP85 threshold record from an explicit finite majorant proof.

The source-extraction and dictionary fields remain explicit.  The strong
`summability` field, however, is no longer assumed: it is proved by
`cmp116Eq229Summability_of_product_majorant`. -/
theorem CammarotaCMP85Threshold.of_product_majorant
    {σ ιD ιY : Type*}
    {theoremStatementExtracted sourceConstantsMatchCMP116 dstageDictionary : Prop}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (majorant : σ → ιD → ℝ)
    (htheoremStatementExtracted : theoremStatementExtracted)
    (hsourceConstantsMatchCMP116 : sourceConstantsMatchCMP116)
    (hdstageDictionary : dstageDictionary)
    (hprod :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          majorant Y0 D)
    (hmajorant :
      ∀ Y0, Finset.sum (DIndex Y0) (fun D => majorant Y0 D) ≤ 1) :
    CammarotaCMP85Threshold
      theoremStatementExtracted sourceConstantsMatchCMP116 dstageDictionary
      DIndex DParts alpha6 delta kappa metric := by
  refine
    { theorem_statement_extracted := htheoremStatementExtracted
      source_constants_match_cmp116 := hsourceConstantsMatchCMP116
      dstage_dictionary := hdstageDictionary
      summability := ?_ }
  exact
    cmp116Eq229Summability_of_product_majorant
      DIndex DParts alpha6 delta kappa metric majorant hprod hmajorant

/-- Uniform cardinality version of
`CammarotaCMP85Threshold.of_product_majorant`.

This is the smallest practical replacement for the old landing-pad usage: prove
the Cammarota/source metadata and the concrete inequalities
`product <= bound` and `|DIndex| * bound <= 1`; Lean then constructs the full
threshold package, including Eq. (2.29) summability. -/
theorem CammarotaCMP85Threshold.of_uniform_product_bound
    {σ ιD ιY : Type*}
    {theoremStatementExtracted sourceConstantsMatchCMP116 dstageDictionary : Prop}
    (DIndex : σ → Finset ιD)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (bound : σ → ℝ)
    (htheoremStatementExtracted : theoremStatementExtracted)
    (hsourceConstantsMatchCMP116 : sourceConstantsMatchCMP116)
    (hdstageDictionary : dstageDictionary)
    (hprod :
      ∀ Y0 D, D ∈ DIndex Y0 →
        cmp116Eq229Product DParts alpha6 delta kappa metric Y0 D ≤
          bound Y0)
    (hcard :
      ∀ Y0, ((DIndex Y0).card : ℝ) * bound Y0 ≤ 1) :
    CammarotaCMP85Threshold
      theoremStatementExtracted sourceConstantsMatchCMP116 dstageDictionary
      DIndex DParts alpha6 delta kappa metric := by
  refine
    CammarotaCMP85Threshold.of_product_majorant
      DIndex DParts alpha6 delta kappa metric
      (fun Y0 _D => bound Y0)
      htheoremStatementExtracted hsourceConstantsMatchCMP116 hdstageDictionary
      hprod ?_
  intro Y0
  calc
    Finset.sum (DIndex Y0) (fun _D => bound Y0) =
        ((DIndex Y0).card : ℝ) * bound Y0 := by
          simp
    _ ≤ 1 := hcard Y0

end YangMills.RG
