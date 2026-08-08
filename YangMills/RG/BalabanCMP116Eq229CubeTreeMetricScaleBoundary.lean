/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229CubeTreeMetric
import YangMills.RG.BalabanCMP116Lemma3ScaleFamily

/-!
# Physical-cube source-tree equation-(2.29) scale boundary

This is the type-correct bridge from the constructed CMP116 source tree
metric to the literal `Cube 4 L` indices used by the equation-(2.26) and
Lemma-3 physical contour pipeline.

The caller identifies its `DIndex` with an exact-union fiber of nonempty
face-connected physical cube domains.  Equation (2.27), equation (2.29), the
shifted equation-(2.30) comparison, and the metric are generated internally.
-/

namespace YangMills.RG

open Finset

/-- Construct the full equation-(2.29) scale boundary on literal physical
cube indices.  No reindexing equality between `FinBox` and `Cube` families
appears in the interface. -/
theorem CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_exactUnion
    {σ ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc L : ℕ} [NeZero N] [NeZero L]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k)
          (Finset (Finset (Cube 4 L)))
          (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts :
      ∀ t k, σ t k →
        Finset (Finset (Cube 4 L)) →
          Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧
          walkConnected (cmp116CubeFaceAdj L) Y)
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
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) := by
  refine ⟨?_, halpha6⟩
  intro t k Z
  have hsummable :=
    cmp116Eq229ExactUnion_sum_prod_le_one_cubeSourceTreeMetric_uniform
      (domainFamily t k)
      (unionOf t k Z)
      (hunion_nonempty t k Z)
      (hdomains t k)
      (alpha6 t k)
      (hp t k).delta
      (hp t k).kappa
      (halpha6 t k)
      (hdeltaKappa t k)
      (hCq t k)
      (huniform t k)
  rw [hDIndex t k Z]
  simpa [hDParts] using hsummable

/-- Construct the physical equation-(2.29) boundary when a physical `D`
index is represented by its finite family of connected localization-domain
components.

The three dictionary hypotheses state exactly that `DParts` restricts to a
bijection from the physical `DIndex` to the exact-union fiber.  In particular,
the theorem does not identify a physical `D` with a family of domains, and it
does not assume equation (2.29) under another name. -/
theorem CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_componentExactUnion
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc L : ℕ} [NeZero N] [NeZero L]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k)
          (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts :
      ∀ t k, σ t k → ιD t k →
        Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧
          walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ (R t k).DIndex Z →
        ∀ D₂, D₂ ∈ (R t k).DIndex Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
    (hparts_surj :
      ∀ t k Z parts,
        parts ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z) →
        ∃ D, D ∈ (R t k).DIndex Z ∧
          DParts t k Z D = parts)
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
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) := by
  refine ⟨?_, halpha6⟩
  intro t k Z
  have hsummable :=
    cmp116Eq229ExactUnion_sum_prod_le_one_cubeSourceTreeMetric_uniform
      (domainFamily t k)
      (unionOf t k Z)
      (hunion_nonempty t k Z)
      (hdomains t k)
      (alpha6 t k)
      (hp t k).delta
      (hp t k).kappa
      (halpha6 t k)
      (hdeltaKappa t k)
      (hCq t k)
      (huniform t k)
  calc
    (∑ D ∈ (R t k).DIndex Z,
        ∏ Y ∈ DParts t k Z D,
          cmp116Eq229Weight
            (alpha6 t k) (hp t k).delta (hp t k).kappa
            cmp116CubeSourceTreeMetric Y) =
      ∑ parts ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z),
        ∏ Y ∈ parts,
          cmp116Eq229Weight
            (alpha6 t k) (hp t k).delta (hp t k).kappa
            cmp116CubeSourceTreeMetric Y := by
      refine Finset.sum_bij
        (fun D hD => DParts t k Z D) ?_ ?_ ?_ ?_
      · intro D hD
        exact hparts_mem t k Z D hD
      · intro D₁ hD₁ D₂ hD₂ heq
        exact hparts_inj t k Z D₁ hD₁ D₂ hD₂ heq
      · intro parts hparts
        obtain ⟨D, hD, hDParts⟩ :=
          hparts_surj t k Z parts hparts
        exact ⟨D, hD, hDParts⟩
      · intro D hD
        rfl
    _ ≤ 1 := hsummable

/-- Construct the physical equation-(2.29) boundary when each physical `D`
index maps injectively into the exact-union fiber.

Surjectivity onto every exact-union subfamily is unnecessary: the omitted
terms are nonnegative, so the physical sum is bounded by the full source
fiber.  This is the source-faithful interface when the physical index selects
only some exact-union domain families. -/
theorem CMP116Lemma3Eq229ScaleBoundary.of_cubeSourceTreeMetric_exactUnionInjection
    {σ ιD ιP ιZ0 ιZ0' : ℕ → ℕ → Type*}
    {dPhys N Nc L : ℕ} [NeZero N] [NeZero L]
    (hp : ∀ _ _, CMP116Lemma3Parameters)
    (R :
      ∀ t k,
        CMP116HResummation
          (σ t k) (ιD t k)
          (ιP t k) (ιZ0 t k) (ιZ0' t k)
          (PhysicalGaugeField dPhys N Nc)
          (PhysicalGaugeField dPhys N Nc))
    (DParts :
      ∀ t k, σ t k → ιD t k →
        Finset (Finset (Cube 4 L)))
    (domainFamily :
      ∀ _t _k, Finset (Finset (Cube 4 L)))
    (unionOf :
      ∀ t k, σ t k → Finset (Cube 4 L))
    (hunion_nonempty :
      ∀ t k Z, (unionOf t k Z).Nonempty)
    (hdomains :
      ∀ t k Y, Y ∈ domainFamily t k →
        Y.Nonempty ∧
          walkConnected (cmp116CubeFaceAdj L) Y)
    (hparts_mem :
      ∀ t k Z D, D ∈ (R t k).DIndex Z →
        DParts t k Z D ∈
          cmp116Eq229ExactUnionDIndex
            (domainFamily t k) (unionOf t k Z))
    (hparts_inj :
      ∀ t k Z D₁, D₁ ∈ (R t k).DIndex Z →
        ∀ D₂, D₂ ∈ (R t k).DIndex Z →
          DParts t k Z D₁ = DParts t k Z D₂ →
            D₁ = D₂)
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
      (fun _t _k _Z Y => cmp116CubeSourceTreeMetric Y) := by
  classical
  refine ⟨?_, halpha6⟩
  intro t k Z
  let fiber :=
    cmp116Eq229ExactUnionDIndex
      (domainFamily t k) (unionOf t k Z)
  let mapped :=
    ((R t k).DIndex Z).image (DParts t k Z)
  let term : Finset (Finset (Cube 4 L)) → ℝ :=
    fun parts =>
      ∏ Y ∈ parts,
        cmp116Eq229Weight
          (alpha6 t k) (hp t k).delta (hp t k).kappa
          cmp116CubeSourceTreeMetric Y
  have hsummable :
      (∑ parts ∈ fiber, term parts) ≤ 1 := by
    simpa [fiber, term] using
      (cmp116Eq229ExactUnion_sum_prod_le_one_cubeSourceTreeMetric_uniform
        (domainFamily t k)
        (unionOf t k Z)
        (hunion_nonempty t k Z)
        (hdomains t k)
        (alpha6 t k)
        (hp t k).delta
        (hp t k).kappa
        (halpha6 t k)
        (hdeltaKappa t k)
        (hCq t k)
        (huniform t k))
  have hmapped_subset : mapped ⊆ fiber := by
    intro parts hparts
    rcases Finset.mem_image.mp hparts with ⟨D, hD, rfl⟩
    exact hparts_mem t k Z D hD
  have hsum_eq :
      (∑ D ∈ (R t k).DIndex Z, term (DParts t k Z D)) =
        ∑ parts ∈ mapped, term parts := by
    rw [Finset.sum_image]
    intro D₁ hD₁ D₂ hD₂ heq
    exact hparts_inj t k Z D₁ hD₁ D₂ hD₂ heq
  calc
    (∑ D ∈ (R t k).DIndex Z,
        ∏ Y ∈ DParts t k Z D,
          cmp116Eq229Weight
            (alpha6 t k) (hp t k).delta (hp t k).kappa
            cmp116CubeSourceTreeMetric Y) =
      ∑ parts ∈ mapped, term parts := by
        simpa [term] using hsum_eq
    _ ≤ ∑ parts ∈ fiber, term parts :=
      Finset.sum_le_sum_of_subset_of_nonneg hmapped_subset
        (fun parts _hparts _hmissing =>
          Finset.prod_nonneg fun Y _hY =>
            cmp116Eq229Weight_nonneg (halpha6 t k) Y)
    _ ≤ 1 := hsummable

end YangMills.RG
