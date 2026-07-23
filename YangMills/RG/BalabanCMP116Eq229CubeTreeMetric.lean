/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq230TreeMetric

/-!
# The CMP116 source-tree metric on the physical `Cube` type

The source geometry for equation (2.30) was constructed on
`FinBox 4 L = Fin 4 → Fin L`, while the physical Lemma-3 pipeline uses
`Cube 4 L = Fin 4 → ZMod L`.  This file identifies those finite periodic
lattices exactly, transports the face graph, and pulls the source tree metric
back to the physical cube type.

No metric comparison is assumed: the shifted equation-(2.30) estimate is
transported from the constructed cube-edge tree metric.
-/

namespace YangMills.RG

open Finset

/-- Coordinatewise identification of the two periodic lattice types used by
the source geometry and the physical activity pipeline. -/
def cmp116FinBoxCubeEquiv (L : ℕ) [NeZero L] :
    FinBox 4 L ≃ Cube 4 L where
  toFun x i := ZMod.finEquiv L (x i)
  invFun x i := (ZMod.finEquiv L).symm (x i)
  left_inv x := by
    funext i
    exact (ZMod.finEquiv L).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (ZMod.finEquiv L).apply_symm_apply (x i)

/-- Face adjacency on physical cubes, defined as the exact pullback of the
CMP116 coarse face graph. -/
def cmp116CubeFaceAdj (L : ℕ) [NeZero L] : SimpleGraph (Cube 4 L) :=
  (cmp116CoarseFaceAdj 4 L).comap (cmp116FinBoxCubeEquiv L).symm

instance cmp116CubeFaceAdj_decidableRel (L : ℕ) [NeZero L] :
    DecidableRel (cmp116CubeFaceAdj L).Adj := by
  intro x y
  change Decidable
    ((cmp116CoarseFaceAdj 4 L).Adj
      ((cmp116FinBoxCubeEquiv L).symm x)
      ((cmp116FinBoxCubeEquiv L).symm y))
  infer_instance

/-- The transported physical face graph retains the source degree bound. -/
theorem cmp116CubeFaceAdj_degree_le_eight
    (L : ℕ) [NeZero L] (x : Cube 4 L) :
    (cmp116CubeFaceAdj L).degree x ≤ 8 := by
  let e : Cube 4 L ≃ FinBox 4 L := (cmp116FinBoxCubeEquiv L).symm
  let iso :
      cmp116CubeFaceAdj L ≃g cmp116CoarseFaceAdj 4 L :=
    SimpleGraph.Iso.comap e (cmp116CoarseFaceAdj 4 L)
  have hdegree :
      (cmp116CoarseFaceAdj 4 L).degree (e x) =
        (cmp116CubeFaceAdj L).degree x := by
    simpa [cmp116CubeFaceAdj, e, iso] using
      (SimpleGraph.Iso.degree_eq iso x)
  rw [← hdegree]
  exact cmp116CoarseFaceAdj_degree_le_eight L (e x)

/-- Pull a physical cube family back to the `FinBox` source coordinates. -/
def cmp116CubeFamilyToFinBox
    {L : ℕ} [NeZero L] (Y : Finset (Cube 4 L)) :
    Finset (FinBox 4 L) :=
  Y.map (cmp116FinBoxCubeEquiv L).symm.toEmbedding

@[simp]
theorem card_cmp116CubeFamilyToFinBox
    {L : ℕ} [NeZero L] (Y : Finset (Cube 4 L)) :
    (cmp116CubeFamilyToFinBox Y).card = Y.card := by
  simp [cmp116CubeFamilyToFinBox]

theorem nonempty_cmp116CubeFamilyToFinBox
    {L : ℕ} [NeZero L] {Y : Finset (Cube 4 L)}
    (hY : Y.Nonempty) :
    (cmp116CubeFamilyToFinBox Y).Nonempty := by
  obtain ⟨x, hx⟩ := hY
  exact ⟨(cmp116FinBoxCubeEquiv L).symm x, by
    rw [cmp116CubeFamilyToFinBox, Finset.mem_map]
    exact ⟨x, hx, rfl⟩⟩

/-- Walk connectivity is preserved by the exact graph isomorphism. -/
theorem walkConnected_cmp116CubeFamilyToFinBox
    {L : ℕ} [NeZero L] {Y : Finset (Cube 4 L)}
    (hY : walkConnected (cmp116CubeFaceAdj L) Y) :
    walkConnected
      (cmp116CoarseFaceAdj 4 L)
      (cmp116CubeFamilyToFinBox Y) := by
  classical
  let e : Cube 4 L ≃ FinBox 4 L := (cmp116FinBoxCubeEquiv L).symm
  let iso :
      cmp116CubeFaceAdj L ≃g cmp116CoarseFaceAdj 4 L :=
    SimpleGraph.Iso.comap e (cmp116CoarseFaceAdj 4 L)
  intro x hx y hy
  rw [cmp116CubeFamilyToFinBox, Finset.mem_map] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨w, hw⟩ := hY x₀ hx₀ y₀ hy₀
  refine ⟨w.map iso.toHom, ?_⟩
  intro v hv
  have hv' : v ∈ w.support.map iso := by
    have hsupp :
        (w.map iso.toHom).support =
          w.support.map iso.toHom :=
      SimpleGraph.Walk.support_map iso.toHom w
    exact hsupp ▸ hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv'
  rw [cmp116CubeFamilyToFinBox, Finset.mem_map]
  exact ⟨u, hw u hu, rfl⟩

/-- The source tree metric expressed on the physical cube type. -/
noncomputable def cmp116CubeSourceTreeMetric
    {L : ℕ} [NeZero L] (Y : Finset (Cube 4 L)) : ℕ :=
  cmp116SourceTreeMetric (cmp116CubeFamilyToFinBox Y)

/-- The physical source tree metric satisfies the convention-robust source
comparison with no external metric hypothesis. -/
theorem cmp116CubeSourceTreeMetric_eq230_shifted
    {L : ℕ} [NeZero L]
    (Y : Finset (Cube 4 L))
    (hY : Y.Nonempty)
    (hconn : walkConnected (cmp116CubeFaceAdj L) Y) :
    (Y.card : ℝ) / 24 ≤
      (cmp116CubeSourceTreeMetric Y : ℝ) + 1 := by
  have hsource :=
    cmp116SourceTreeMetric_eq230_shifted
      (cmp116CubeFamilyToFinBox Y)
      (nonempty_cmp116CubeFamilyToFinBox hY)
      (walkConnected_cmp116CubeFamilyToFinBox hconn)
  simpa [cmp116CubeSourceTreeMetric] using hsource

/-- The convention-robust equation-(2.29) estimate only needs a finite
degree-eight graph.  This is the graph-generic form used to avoid transporting
nested exact-union sums between equivalent lattice types. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_shiftedCardMetric_uniform_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    (hdegree : ∀ x, G.degree x ≤ 8)
    (alpha6 delta kappa : ℝ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
      1 := by
  apply
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq227_and_localSmallness
      domainFamily Y0 hY0 alpha6 delta kappa
      cmp116Eq229ShiftedCardMetric
      halpha6 hdeltaKappa
      (fun D hD =>
        cmp116Eq229ShiftedCardMetric_eq227
          domainFamily (fun Y hY => (hdomains Y hY).1)
          Y0 hY0 D hD)
  have hlocal :=
    cmp116Eq229_localHalfFugacitySum_le_shifted
      domainFamily Y0 hdomains alpha6 delta kappa
      halpha6 hdeltaKappa
      (Δ := 8)
      hdegree
      (by norm_num)
      (by
        norm_num at hCq ⊢
        exact hCq)
  have hsmall :=
    cmp116Eq229_shifted_localSmallness_of_uniform
      alpha6 delta kappa Y0.card
      (cmp116Eq229ShiftedCardMetric Y0)
      halpha6 hdeltaKappa
      (card_div_twentyFour_le_shiftedCardMetric_add_one Y0)
      hCq huniform
  have hlocal' :
      (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          cmp116Eq229HalfFugacityWeight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
        (alpha6 * Real.exp (3 * (delta * kappa))) *
          ((Y0.card : ℝ) *
            (1 -
              64 * Real.exp (-((delta * kappa) / 48)))⁻¹) := by
    norm_num at hlocal ⊢
    exact hlocal
  calc
    Real.exp
          (-((delta * kappa) / 2) *
            ((cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5)) *
        (Real.exp
            (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
              cmp116Eq229HalfFugacityWeight
                alpha6 delta kappa
                cmp116Eq229ShiftedCardMetric Y) -
          1) ≤
      Real.exp
          (-((delta * kappa) / 2) *
            ((cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (3 * (delta * kappa))) *
              ((Y0.card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) := by
            exact mul_le_mul_of_nonneg_left
              (sub_le_sub_right (Real.exp_le_exp.mpr hlocal') 1)
              (Real.exp_nonneg _)
    _ ≤ 1 := hsmall

/-- Physical equation-(2.29) on an arbitrary finite degree-eight graph,
derived from a shifted source-metric comparison. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230Shifted_uniform_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    (hdegree : ∀ x, G.degree x ≤ 8)
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230Shifted :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ) + 1)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      1 := by
  calc
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      ∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y := by
      refine Finset.sum_le_sum fun D hD => ?_
      have hsource :=
        (mem_cmp116Eq229ExactUnionDIndex_iff
          domainFamily Y0 D).mp hD |>.1
      exact Finset.prod_le_prod
        (fun Y _hY =>
          cmp116Eq229Weight_nonneg
            (metric := metric) halpha6 Y)
        (fun Y hY =>
          cmp116Eq229Weight_le_shiftedCardMetricWeight_of_eq230Shifted
            alpha6 delta kappa metric Y halpha6 hdeltaKappa
            (hEq230Shifted Y (hsource hY)))
    _ ≤ 1 :=
      cmp116Eq229ExactUnion_sum_prod_le_one_shiftedCardMetric_uniform_degreeEight
        domainFamily Y0 hY0 hdomains hdegree
        alpha6 delta kappa halpha6 hdeltaKappa hCq huniform

/-- Fully constructed source-tree equation-(2.29) estimate on the literal
physical `Cube 4 L` type. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_cubeSourceTreeMetric_uniform
    {L : ℕ} [NeZero L]
    (domainFamily : Finset (Finset (Cube 4 L)))
    (Y0 : Finset (Cube 4 L)) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected (cmp116CubeFaceAdj L) Y)
    (alpha6 delta kappa : ℝ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116CubeSourceTreeMetric Y) ≤
      1 := by
  exact
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230Shifted_uniform_degreeEight
      domainFamily Y0 hY0 hdomains
      (cmp116CubeFaceAdj_degree_le_eight L)
      alpha6 delta kappa cmp116CubeSourceTreeMetric
      halpha6 hdeltaKappa
      (fun Y hY =>
        cmp116CubeSourceTreeMetric_eq230_shifted
          Y (hdomains Y hY).1 (hdomains Y hY).2)
      hCq huniform

end YangMills.RG
