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

end YangMills.RG
