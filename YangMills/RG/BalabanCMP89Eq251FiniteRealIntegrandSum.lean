/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251CentralRealIntegrandBound

/-!
# PRE-VALIDATION: finite real-integrand alias sum in CMP89 (2.51)

The source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

This module performs the exact finite split printed in CMP89 (2.51).  The
zero reciprocal alias contributes the separately sealed central `O(1)` term;
every other alias is bounded by the sealed noncentral product weight, and the
complete product sum is controlled by the already sealed one-dimensional
series.  No alias-cardinality estimate is introduced.

The flowing-mass window is used only for the noncentral aliases.  This module
does not construct the analytic strip or identify the Fourier kernel with the
regional Green.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal finite alias sum of the real integrand in CMP89 (2.51). -/
def cmp89Eq251FiniteRealIntegrandSum
    (d L j : ℕ) (mass a alpha : ℝ) (p : Fin d → ℝ)
    (mu : Fin d) (displacement : Fin d → ℝ) : ℝ :=
  ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
    cmp89Eq251NoncentralRealIntegrand
      d L j mass a alpha p m mu displacement

/-- The explicit uniform majorant obtained after the central/noncentral split
and the exact multidimensional product-series estimate. -/
def cmp89Eq251FiniteRealIntegrandBound
    (d : ℕ) (a alpha : ℝ) : ℝ :=
  cmp89Eq251CentralRealIntegrandConstant d a +
    cmp89Eq251NoncentralRealIntegrandConstant d a alpha *
      (∑' n : ℤ,
        cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) n) ^ d

/-- Exact finite central/noncentral summation step in CMP89 (2.51).  The
central branch occurs once, while the noncentral aliases are absorbed into
the infinite product series without a cardinality loss. -/
theorem cmp89Eq251FiniteRealIntegrandSum_le_bound
    {d L j : ℕ} [NeZero L] (hd : 0 < d)
    {mass a alpha : ℝ} (hmass : 0 < mass)
    (hmassWindow : CMP89Eq251UniformMassWindow mass) (ha : 0 < a)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (mu : Fin d) {displacement : Fin d → ℝ}
    (hdisplacement : 0 < cmp89Eq251EuclideanNorm displacement) :
    cmp89Eq251FiniteRealIntegrandSum
        d L j mass a alpha p mu displacement ≤
      cmp89Eq251FiniteRealIntegrandBound d a alpha := by
  let aliases := cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias : Fin d → ℤ := fun _ => 0
  let integrand : (Fin d → ℤ) → ℝ := fun m =>
    cmp89Eq251NoncentralRealIntegrand
      d L j mass a alpha p m mu displacement
  let weight : (Fin d → ℤ) → ℝ := fun m =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent d alpha) m
  let noncentralConstant :=
    cmp89Eq251NoncentralRealIntegrandConstant d a alpha
  have hzero : zeroAlias ∈ aliases := by
    simpa only [aliases, zeroAlias] using
      zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j
  have hsplit :
      cmp89Eq251FiniteRealIntegrandSum
          d L j mass a alpha p mu displacement =
        (∑ m ∈ aliases.erase zeroAlias, integrand m) +
          cmp89Eq251CentralRealIntegrand
            d L j mass a alpha p mu displacement := by
    have h := Finset.sum_erase_add aliases integrand hzero
    rw [cmp89Eq251FiniteRealIntegrandSum,
      cmp89Eq251CentralRealIntegrand]
    simpa only [aliases, zeroAlias, integrand] using h.symm
  have hconstantNonneg : 0 ≤ noncentralConstant := by
    rw [noncentralConstant,
      cmp89Eq251NoncentralRealIntegrandConstant]
    positivity
  have hnoncentralPointwise :
      ∀ m ∈ aliases.erase zeroAlias,
        integrand m ≤ noncentralConstant * weight m := by
    intro m hm
    have hmParts := Finset.mem_erase.mp hm
    exact cmp89Eq251NoncentralRealIntegrand_le_sourceWeight
      hd hmass hmassWindow ha halpha0 halpha1.le hp hmParts.2
      hmParts.1 mu hdisplacement
  have heraseWeight :
      (∑ m ∈ aliases.erase zeroAlias, weight m) ≤
        ∑ m ∈ aliases, weight m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset zeroAlias aliases)
      (fun m _ _ =>
        cmp89Eq251MultidimensionalAliasWeight_nonneg
          (cmp89Eq251AliasSeriesExponent d alpha) m)
  have hfiniteNoncentral :
      (∑ m ∈ aliases.erase zeroAlias, integrand m) ≤
        noncentralConstant *
          cmp89Eq251CenteredMultidimensionalAliasSum
            d (L ^ j) (cmp89Eq251AliasSeriesExponent d alpha) := by
    calc
      (∑ m ∈ aliases.erase zeroAlias, integrand m) ≤
          ∑ m ∈ aliases.erase zeroAlias,
            noncentralConstant * weight m :=
        Finset.sum_le_sum hnoncentralPointwise
      _ = noncentralConstant *
          (∑ m ∈ aliases.erase zeroAlias, weight m) := by
        rw [Finset.mul_sum]
      _ ≤ noncentralConstant * (∑ m ∈ aliases, weight m) :=
        mul_le_mul_of_nonneg_left heraseWeight hconstantNonneg
      _ = noncentralConstant *
          cmp89Eq251CenteredMultidimensionalAliasSum
            d (L ^ j) (cmp89Eq251AliasSeriesExponent d alpha) := by
        rfl
  have hseries :=
    cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
      (L ^ j) hd halpha1
  have hnoncentral :
      (∑ m ∈ aliases.erase zeroAlias, integrand m) ≤
        noncentralConstant *
          (∑' n : ℤ,
            cmp89Eq251OneDimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent d alpha) n) ^ d :=
    hfiniteNoncentral.trans
      (mul_le_mul_of_nonneg_left hseries hconstantNonneg)
  have hcentral := cmp89Eq251CentralRealIntegrand_le_constant
    (d := d) (L := L) (j := j) hmass ha halpha0 halpha1.le hp mu
    hdisplacement
  rw [hsplit, cmp89Eq251FiniteRealIntegrandBound]
  calc
    (∑ m ∈ aliases.erase zeroAlias, integrand m) +
        cmp89Eq251CentralRealIntegrand
          d L j mass a alpha p mu displacement ≤
      noncentralConstant *
          (∑' n : ℤ,
            cmp89Eq251OneDimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent d alpha) n) ^ d +
        cmp89Eq251CentralRealIntegrandConstant d a :=
      add_le_add hnoncentral hcentral
    _ = cmp89Eq251CentralRealIntegrandConstant d a +
        cmp89Eq251NoncentralRealIntegrandConstant d a alpha *
          (∑' n : ℤ,
            cmp89Eq251OneDimensionalAliasWeight
              (cmp89Eq251AliasSeriesExponent d alpha) n) ^ d := by
      rw [noncentralConstant]
      ac_rfl

end

end YangMills.RG
