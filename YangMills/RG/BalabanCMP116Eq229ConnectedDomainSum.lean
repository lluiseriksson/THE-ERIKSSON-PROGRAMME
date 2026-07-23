/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AnimalTour
import YangMills.RG.BalabanCMP116Eq219SourceGeometry
import YangMills.RG.BalabanCMP116Eq229ExactUnionFiber

/-!
# Connected-domain entropy for CMP116 equation (2.29)

After the source-correct exact-union split, equation (2.29) requires a local
sum over nonempty connected domains contained in the fixed union `Y₀`.
This file derives that finite sum from the repository's rooted lattice-animal
theorem.

Every connected domain contained in `Y₀` is overcounted by choosing one of its
vertices as a root.  For each root the full connected-animal sum is bounded by

`(1 - Δ² q)⁻¹`.

Consequently the local sum is at most

`|Y₀| (1 - Δ² q)⁻¹`,

uniformly in the ambient finite volume.  No cardinality of the ambient graph
appears.

Honest scope: this module is graph-theoretic.  A later source dictionary must
instantiate the graph with the four-dimensional coarse face graph, prove its
degree bound, and use equation (2.30) to dominate the half-fugacity weight by
`q ^ |Y|`.
-/

namespace YangMills.RG

open scoped BigOperators
open Finset SimpleGraph

/-- A finite family of nonempty connected domains contained in `Y₀` is
controlled by the rooted lattice-animal sum, with one possible root for each
vertex of `Y₀`. -/
theorem connectedDomainFamily_sum_pow_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    {Δ : ℕ} {q : ℝ}
    (hΔ : ∀ x, G.degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hq0 : 0 ≤ q)
    (hCq : (Δ : ℝ) ^ 2 * q < 1) :
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        q ^ Y.card) ≤
      (Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
  classical
  let relevant := domainFamily.filter fun Y => Y ⊆ Y0
  let rootedAt : V → Finset (Finset V) := fun r =>
    domainFamily.filter fun Y => r ∈ Y
  have hpow_nonneg : ∀ Y : Finset V, 0 ≤ q ^ Y.card :=
    fun Y => pow_nonneg hq0 _
  have hsub :
      relevant ⊆ Y0.biUnion rootedAt := by
    intro Y hY
    have hYmem := Finset.mem_filter.mp hY
    obtain ⟨r, hrY⟩ := (hdomains Y hYmem.1).1
    have hrY0 := hYmem.2 hrY
    rw [Finset.mem_biUnion]
    exact ⟨r, hrY0, by
      rw [Finset.mem_filter]
      exact ⟨hYmem.1, hrY⟩⟩
  have hsub_sum :
      (∑ Y ∈ relevant, q ^ Y.card) ≤
        ∑ Y ∈ Y0.biUnion rootedAt, q ^ Y.card := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun Y _ _ => hpow_nonneg Y)
  have hbi :
      (∑ Y ∈ Y0.biUnion rootedAt, q ^ Y.card) ≤
        ∑ r ∈ Y0, ∑ Y ∈ rootedAt r, q ^ Y.card := by
    exact sum_biUnion_le Y0 rootedAt
      (fun Y => q ^ Y.card) hpow_nonneg
  have hroot :
      ∀ r : V,
        (∑ Y ∈ rootedAt r, q ^ Y.card) ≤
          (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
    intro r
    let full : Finset (Finset V) :=
      Finset.univ.filter fun Y =>
        r ∈ Y ∧
          ∀ x ∈ Y, ∃ w : G.Walk r x, IsSWalk Y w
    have hrooted_sub : rootedAt r ⊆ full := by
      intro Y hY
      have hYmem := Finset.mem_filter.mp hY
      have hconn := (hdomains Y hYmem.1).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ Y, hYmem.2, ?_⟩
      intro x hx
      obtain ⟨w, hw⟩ := hconn r hYmem.2 x hx
      exact ⟨w, hw⟩
    have hfinite :
        (∑ Y ∈ rootedAt r, q ^ Y.card) ≤
          ∑ Y ∈ full, q ^ Y.card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hrooted_sub
        (fun Y _ _ => hpow_nonneg Y)
    have hfull_eq :
        (∑ Y ∈ full, q ^ Y.card) =
          ∑ A : {Y : Finset V //
              r ∈ Y ∧
                ∀ x ∈ Y, ∃ w : G.Walk r x, IsSWalk Y w},
            q ^ (A : Finset V).card := by
      exact Finset.sum_subtype full (fun Y => by simp [full])
        (fun Y => q ^ Y.card)
    have hanimal :=
      rooted_connected_weight_summable
        (G := G) (r := r) hΔ hΔ1 hq0 hCq
    exact hfinite.trans (hfull_eq.trans_le (by
      simpa [tsum_fintype] using hanimal))
  calc
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        q ^ Y.card) =
        ∑ Y ∈ relevant, q ^ Y.card := by rfl
    _ ≤ ∑ Y ∈ Y0.biUnion rootedAt, q ^ Y.card := hsub_sum
    _ ≤ ∑ r ∈ Y0, ∑ Y ∈ rootedAt r, q ^ Y.card := hbi
    _ ≤ ∑ _r ∈ Y0, (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
      exact Finset.sum_le_sum fun r _hr => hroot r
    _ = (Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
      simp [nsmul_eq_mul]

/-- Equation (2.30), in the form `|Y| / 24 ≤ d_k(Y)`, turns the half-fugacity
weight into a pure block-cardinality weight.

The number `24 = 3 * 2^3` is the literal four-dimensional constant printed in
CMP116 equation (2.30). -/
theorem cmp116Eq229HalfFugacityWeight_le_cardWeight_of_eq230
    {V : Type*}
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (Y : Finset V)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230 : (Y.card : ℝ) / 24 ≤ (metric Y : ℝ)) :
    cmp116Eq229HalfFugacityWeight alpha6 delta kappa metric Y ≤
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
        Real.exp (-((delta * kappa) / 48)) ^ Y.card := by
  rw [cmp116Eq229HalfFugacityWeight]
  have hexp :
      Real.exp
          (((delta * kappa) / 2) * (5 - (metric Y : ℝ))) ≤
        Real.exp (5 * (delta * kappa) / 2) *
          Real.exp (-((delta * kappa) / 48)) ^ Y.card := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled :
        ((delta * kappa) / 2) * ((Y.card : ℝ) / 24) ≤
          ((delta * kappa) / 2) * (metric Y : ℝ) :=
      mul_le_mul_of_nonneg_left hEq230
        (div_nonneg hdeltaKappa (by norm_num))
    nlinarith
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hexp halpha6

/-- Connected-domain entropy plus equation (2.30) bounds the full local
half-fugacity sum by an explicit volume-uniform expression.

Only `|Y₀|`, not the ambient volume, remains. -/
theorem cmp116Eq229_localHalfFugacitySum_le_of_connectedDomains_eq230
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    {Δ : ℕ}
    (hΔ : ∀ x, G.degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hCq :
      (Δ : ℝ) ^ 2 * Real.exp (-((delta * kappa) / 48)) < 1) :
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
          alpha6 delta kappa metric Y) ≤
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
        ((Y0.card : ℝ) *
          (1 -
            (Δ : ℝ) ^ 2 *
              Real.exp (-((delta * kappa) / 48)))⁻¹) := by
  let q : ℝ := Real.exp (-((delta * kappa) / 48))
  let prefactor : ℝ :=
    alpha6 * Real.exp (5 * (delta * kappa) / 2)
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hprefactor : 0 ≤ prefactor :=
    mul_nonneg halpha6 (Real.exp_nonneg _)
  have hpoint :
      ∀ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
            alpha6 delta kappa metric Y ≤
          prefactor * q ^ Y.card := by
    intro Y hY
    have hYsource := (Finset.mem_filter.mp hY).1
    simpa [q, prefactor] using
      cmp116Eq229HalfFugacityWeight_le_cardWeight_of_eq230
        alpha6 delta kappa metric Y halpha6 hdeltaKappa
        (hEq230 Y hYsource)
  have hanimal :
      (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          q ^ Y.card) ≤
        (Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹ :=
    connectedDomainFamily_sum_pow_card_le
      domainFamily Y0 hdomains hΔ hΔ1 hq0 (by simpa [q] using hCq)
  calc
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
          alpha6 delta kappa metric Y) ≤
      ∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        prefactor * q ^ Y.card := by
          exact Finset.sum_le_sum fun Y hY => hpoint Y hY
    _ =
      prefactor *
        (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          q ^ Y.card) := by
            rw [Finset.mul_sum]
    _ ≤
      prefactor *
        ((Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹) :=
          mul_le_mul_of_nonneg_left hanimal hprefactor
    _ =
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
        ((Y0.card : ℝ) *
          (1 -
            (Δ : ℝ) ^ 2 *
              Real.exp (-((delta * kappa) / 48)))⁻¹) := by
          rfl

/-- Source-level completion of the equation-(2.29) fiber estimate from:

* exact union and equation (2.27);
* connected domains;
* the equation-(2.30) metric/cardinality comparison;
* the bounded-degree lattice-animal theorem; and
* one explicit final scalar smallness inequality.

No form of equation (2.29) occurs among the hypotheses. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_of_sourceGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq227 :
      ∀ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        (metric Y0 : ℝ) + 5 ≤
          ∑ Y ∈ D, ((metric Y : ℝ) + 5))
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    {Δ : ℕ}
    (hΔ : ∀ x, G.degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hCq :
      (Δ : ℝ) ^ 2 * Real.exp (-((delta * kappa) / 48)) < 1)
    (hsmall :
      Real.exp
          (-((delta * kappa) / 2) * ((metric Y0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
              ((Y0.card : ℝ) *
                (1 -
                  (Δ : ℝ) ^ 2 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
        1) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      1 := by
  have hlocal :=
    cmp116Eq229_localHalfFugacitySum_le_of_connectedDomains_eq230
      domainFamily Y0 hdomains alpha6 delta kappa metric
      halpha6 hdeltaKappa hEq230 hΔ hΔ1 hCq
  apply
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq227_and_localSmallness
      domainFamily Y0 hY0 alpha6 delta kappa metric
      halpha6 hdeltaKappa hEq227
  calc
    Real.exp
          (-((delta * kappa) / 2) * ((metric Y0 : ℝ) + 5)) *
        (Real.exp
            (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
              cmp116Eq229HalfFugacityWeight
                alpha6 delta kappa metric Y) -
          1) ≤
      Real.exp
          (-((delta * kappa) / 2) * ((metric Y0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
              ((Y0.card : ℝ) *
                (1 -
                  (Δ : ℝ) ^ 2 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) := by
            exact mul_le_mul_of_nonneg_left
              (sub_le_sub_right (Real.exp_le_exp.mpr hlocal) 1)
              (Real.exp_nonneg _)
    _ ≤ 1 := hsmall

/-- Four-dimensional CMP116 specialization.

The coarse face-graph degree is discharged internally as `8`, so the
lattice-animal denominator is the explicit source-independent expression

`1 - 64 * exp (-(delta*kappa)/48)`.

No graph-degree certificate remains in the interface. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (Y0 : Finset (FinBox 4 N')) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset (FinBox 4 N') → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq227 :
      ∀ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        (metric Y0 : ℝ) + 5 ≤
          ∑ Y ∈ D, ((metric Y : ℝ) + 5))
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (hsmall :
      Real.exp
          (-((delta * kappa) / 2) * ((metric Y0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
              ((Y0.card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
        1) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      1 := by
  apply
    cmp116Eq229ExactUnion_sum_prod_le_one_of_sourceGeometry
      (G := cmp116CoarseFaceAdj 4 N')
      domainFamily Y0 hY0 hdomains alpha6 delta kappa metric
      halpha6 hdeltaKappa hEq227 hEq230
      (Δ := 8)
      (cmp116CoarseFaceAdj_degree_le_eight N')
      (by norm_num)
  · norm_num at hCq ⊢
    exact hCq
  · norm_num at hsmall ⊢
    exact hsmall

end YangMills.RG
