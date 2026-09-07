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

/-- A finite family of connected domains containing one fixed root is
controlled by the rooted lattice-animal sum.

Unlike `connectedDomainFamily_sum_pow_card_le`, this form does not require the
domains to be contained in a common carrier.  It is the source-faithful
estimate needed when a terminal ledger retains every native localization
domain as a distinct index and only coarsens its physical support. -/
theorem connectedDomainFamily_rooted_sum_pow_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (r : V)
    (hdomains :
      ∀ Y ∈ domainFamily,
        walkConnected G Y)
    {Δ : ℕ} {q : ℝ}
    (hΔ : ∀ x, G.degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hq0 : 0 ≤ q)
    (hCq : (Δ : ℝ) ^ 2 * q < 1) :
    (∑ Y ∈ domainFamily.filter (fun Y => r ∈ Y),
        q ^ Y.card) ≤
      (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
  classical
  let rootedAt : Finset (Finset V) :=
    domainFamily.filter fun Y => r ∈ Y
  let full : Finset (Finset V) :=
    Finset.univ.filter fun Y =>
      r ∈ Y ∧
        ∀ x ∈ Y, ∃ w : G.Walk r x, IsSWalk Y w
  have hpow_nonneg : ∀ Y : Finset V, 0 ≤ q ^ Y.card :=
    fun Y => pow_nonneg hq0 _
  have hrooted_sub : rootedAt ⊆ full := by
    intro Y hY
    have hYmem := Finset.mem_filter.mp hY
    have hconn := hdomains Y hYmem.1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ Y, hYmem.2, ?_⟩
    intro x hx
    obtain ⟨w, hw⟩ := hconn r hYmem.2 x hx
    exact ⟨w, hw⟩
  have hfinite :
      (∑ Y ∈ rootedAt, q ^ Y.card) ≤
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
  calc
    (∑ Y ∈ domainFamily.filter (fun Y => r ∈ Y),
        q ^ Y.card) =
        ∑ Y ∈ rootedAt, q ^ Y.card := by rfl
    _ ≤ ∑ Y ∈ full, q ^ Y.card := hfinite
    _ ≤ (1 - (Δ : ℝ) ^ 2 * q)⁻¹ := by
      exact hfull_eq.trans_le (by
        simpa [tsum_fintype] using hanimal)

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

/-- A uniform source-smallness condition implies the `Y₀`-dependent scalar
inequality left by the exact-union/animal estimate.

The proof uses equation (2.30) once more for `Y₀`.  If

`24 * alpha6 * exp (5 lambda / 2) / (1 - 64 exp (-lambda/48))
  ≤ lambda/2`,

then the positive local-domain entropy is absorbed by half of the metric
decay.  The remaining shifted factor is at most `exp (-5 lambda/2) ≤ 1`. -/
theorem cmp116Eq229_fourDimensional_localSmallness_of_uniform
    (alpha6 delta kappa : ℝ)
    (Y0card metricY0 : ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230Y0 : (Y0card : ℝ) / 24 ≤ (metricY0 : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    Real.exp
          (-((delta * kappa) / 2) * ((metricY0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
              ((Y0card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
      1 := by
  let halfRate : ℝ := (delta * kappa) / 2
  let entropyCoefficient : ℝ :=
    (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
      (1 -
        64 * Real.exp (-((delta * kappa) / 48)))⁻¹
  let entropy : ℝ := entropyCoefficient * (Y0card : ℝ)
  have hden_pos :
      0 <
        1 - 64 * Real.exp (-((delta * kappa) / 48)) := by
    linarith
  have hcoefficient_nonneg : 0 ≤ entropyCoefficient := by
    exact mul_nonneg
      (mul_nonneg halpha6 (Real.exp_nonneg _))
      (inv_nonneg.mpr hden_pos.le)
  have hhalf_nonneg : 0 ≤ halfRate := by
    exact div_nonneg hdeltaKappa (by norm_num)
  have huniform' : entropyCoefficient * 24 ≤ halfRate := by
    simpa [entropyCoefficient, halfRate, mul_assoc, mul_comm, mul_left_comm]
      using huniform
  have hentropy_le : entropy ≤ halfRate * (metricY0 : ℝ) := by
    have hcard_nonneg : 0 ≤ (Y0card : ℝ) / 24 := by positivity
    have hfirst :
        (entropyCoefficient * 24) * ((Y0card : ℝ) / 24) ≤
          halfRate * ((Y0card : ℝ) / 24) :=
      mul_le_mul_of_nonneg_right huniform' hcard_nonneg
    have hsecond :
        halfRate * ((Y0card : ℝ) / 24) ≤
          halfRate * (metricY0 : ℝ) :=
      mul_le_mul_of_nonneg_left hEq230Y0 hhalf_nonneg
    calc
      entropy =
          (entropyCoefficient * 24) * ((Y0card : ℝ) / 24) := by
            simp [entropy]
            ring
      _ ≤ halfRate * ((Y0card : ℝ) / 24) := hfirst
      _ ≤ halfRate * (metricY0 : ℝ) := hsecond
  have hexponent :
      -(halfRate * ((metricY0 : ℝ) + 5)) + entropy ≤
        -(halfRate * 5) := by
    linarith
  calc
    Real.exp
          (-((delta * kappa) / 2) * ((metricY0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
              ((Y0card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
      Real.exp (-(halfRate * ((metricY0 : ℝ) + 5))) *
        Real.exp entropy := by
          have hsubexp : Real.exp entropy - 1 ≤ Real.exp entropy :=
            sub_le_self _ (by norm_num)
          have hmul :=
            mul_le_mul_of_nonneg_left hsubexp
              (Real.exp_nonneg
                (-(halfRate * ((metricY0 : ℝ) + 5))))
          simpa [halfRate, entropy, entropyCoefficient,
            mul_assoc, mul_comm, mul_left_comm] using hmul
    _ =
      Real.exp
        (-(halfRate * ((metricY0 : ℝ) + 5)) + entropy) := by
          rw [Real.exp_add]
    _ ≤ Real.exp (-(halfRate * 5)) :=
      Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      exact neg_nonpos.mpr (mul_nonneg hhalf_nonneg (by norm_num))
    _ = 1 := Real.exp_zero

/-- Fully uniform four-dimensional fixed-union estimate.

Compared with `cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional`, the
`Y₀`-dependent smallness premise has disappeared.  The only scalar threshold
is the explicit source-uniform condition on `alpha6`, `delta`, and `kappa`. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional_of_uniform
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
    (hEq230Y0 :
      (Y0.card : ℝ) / 24 ≤ (metric Y0 : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      1 := by
  exact
    cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional
      domainFamily Y0 hY0 hdomains alpha6 delta kappa metric
      halpha6 hdeltaKappa hEq227 hEq230 hCq
      (cmp116Eq229_fourDimensional_localSmallness_of_uniform
        alpha6 delta kappa Y0.card (metric Y0)
        halpha6 hdeltaKappa hEq230Y0 hCq huniform)

/-- Source-correct producer for the legacy `CMP116Eq229Summability` consumer
interface.

The context type is the subtype of nonempty fixed unions `Y₀`; its `D` index
is definitionally the exact-union fiber.  Hence this theorem can feed the
existing downstream Lemma-3/KP chain without reverting to the impossible
unrestricted powerset interpretation of equation (2.29). -/
theorem CMP116Eq229Summability.of_exactUnion_fourDimensional_uniform
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset (FinBox 4 N') → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq227 :
      ∀ Y0 : {Y0 : Finset (FinBox 4 N') // Y0.Nonempty},
        ∀ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0.1,
          (metric Y0.1 : ℝ) + 5 ≤
            ∑ Y ∈ D, ((metric Y : ℝ) + 5))
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    (hEq230Union :
      ∀ Y0 : {Y0 : Finset (FinBox 4 N') // Y0.Nonempty},
        (Y0.1.card : ℝ) / 24 ≤ (metric Y0.1 : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    CMP116Eq229Summability
      (fun Y0 : {Y0 : Finset (FinBox 4 N') // Y0.Nonempty} =>
        cmp116Eq229ExactUnionDIndex domainFamily Y0.1)
      (fun _Y0 D => D)
      alpha6 delta kappa
      (fun _Y0 Y => metric Y) := by
  intro Y0
  exact
    cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional_of_uniform
      domainFamily Y0.1 Y0.2 hdomains
      alpha6 delta kappa metric halpha6 hdeltaKappa
      (hEq227 Y0) hEq230 (hEq230Union Y0) hCq huniform

end YangMills.RG
