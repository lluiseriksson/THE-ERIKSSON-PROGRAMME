/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229CubeTreeMetric
import YangMills.RG.BalabanCMP116Lemma3CubeRawBridge

/-!
# Physical CMP116 source-tree metric through Appendix-F KP

This module closes the metric dictionary between the literal dimension-four
CMP116 source-tree decay and the modified metric used by Appendix F.

The two metrics are not compared directly.  Instead equation (2.30) gives the
sharp convention-safe route

`d_M(X) + 1 ≤ |X| ≤ |Y| ≤ 24 * (d_source(Y) + 1)`

for a polymer carrier `X` contained in its connected source domain `Y`.
Consequently the target Appendix-F rate is multiplied by `24`, and the finite
normalization loss is paid explicitly by `exp (24 * targetRate)`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- End-to-end metric conversion from a physical CMP116 source domain to the
bounded-hole Appendix-F KP criterion.

No comparison between `discreteModifiedMetric` and the source-tree metric is
an input.  It is generated from carrier containment, source connectivity, and
the literal equation-(2.30) constant `24`. -/
theorem cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles_of_cubeSourceTreeMetric
    {dPhys N Nc L lieDim : ℕ} [NeZero N] [NeZero L]
    {HF : HoleFamily 4 L}
    {z : ℕ → ℕ → Finset (Cube 4 L) → ℂ}
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _t : ℕ, ∀ _k : ℕ,
      PhysicalGaugeCMP116Dictionary dPhys N Nc 4 L lieDim)
    (physicalActivity :
      ∀ t k, OmegaPolymerType HF (z t k) →
        PhysicalGaugeLocalActivity dPhys N Nc)
    (unionOf :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (hcarrier :
      ∀ t k X, X ∈ Λ t k → X.val ⊆ unionOf t k X)
    (hunion_nonempty :
      ∀ t k X, (unionOf t k X).Nonempty)
    (hunion_connected :
      ∀ t k X,
        walkConnected (cmp116CubeFaceAdj L) (unionOf t k X))
    (blockScale : ℕ → ℕ → ℕ)
    (C3 epsilon1 delta kappaSource : ℕ → ℕ → ℝ)
    (B : ℕ) (kappa0 : ℝ)
    (Omega : ∀ _t _k, Finset (Cube 4 L))
    (activeSupport :
      ∀ t k, OmegaPolymerType HF (z t k) → Finset (Cube 4 L))
    (activity_stronglyMeasurable :
      ∀ t k i, ∀ psi : ∀ _ : Cube 4 L, Fin lieDim → ℝ,
        StronglyMeasurable
          (fun X : ∀ _ : Cube 4 L, Fin lieDim → ℝ =>
            ((D t k).reindexPhysicalActivity
              (physicalActivity t k i)).globalEval psi X))
    (spectatorSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).spectatorSupport ⊆
            activeSupport t k i)
    (fluctuationSupport_subset :
      ∀ t k i,
        ((D t k).reindexPhysicalActivity
          (physicalActivity t k i)).fluctuationSupport ⊆
            Omega t k ∩ activeSupport t k i)
    (estimate :
      CMP116Lemma3ActivityEstimateScaleFamily
        physicalActivity
        (fun t k X => cmp116CubeSourceTreeMetric (unionOf t k X))
        blockScale C3 epsilon1 delta kappaSource)
    (rate_margin :
      ∀ t k,
        24 * (4 * kappa0 + 3 + boundedHoleCardinalityTilt 4 B) ≤
          balabanCMP116Lemma3DecayRate
            (blockScale t k) (delta t k) (kappaSource t k))
    (ν : ℕ → ℕ → Measure (Fin lieDim → ℝ))
    (g : ℕ → ℝ)
    (t0 kScale : ℕ)
    (C Hscale c0 s A : ℝ)
    (hkappa0 : 0 < kappa0)
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hamplitude_one : ∀ t k,
      (C3 t k * epsilon1 t k) *
          Real.exp
            (24 *
              (4 * kappa0 + 3 +
                boundedHoleCardinalityTilt 4 B)) ≤
        1)
    (hhalf : ∀ t k,
      appendixFSecondUrsellLeafConstant 4 kappa0 *
          (2 *
            ((C3 t k * epsilon1 t k) *
              Real.exp
                (24 *
                  (4 * kappa0 + 3 +
                    boundedHoleCardinalityTilt 4 B))) *
            appendixFHoleRootSumConstant 4 kappa0) ≤ 1 / 2)
    (hprofile : ∀ t k,
      4 * appendixFSecondUrsellMomentConstant 4 kappa0 *
          ((C3 t k * epsilon1 t k) *
            Real.exp
              (24 *
                (4 * kappa0 + 3 +
                  boundedHoleCardinalityTilt 4 B))) *
            appendixFHoleRootSumConstant 4 kappa0 ≤
        C * Hscale * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (amplitude_nonneg : ∀ t k, 0 ≤ C3 t k * epsilon1 t k)
    (hdisj :
      ∀ H1 ∈ HF.holes, ∀ H2 ∈ HF.holes,
        H1 ≠ H2 → Disjoint H1 H2)
    (hnoedges : noEdgesBetweenHoles (cubeAdj 4 L) HF.holes)
    (hholes_ne : ∀ H0 ∈ HF.holes, H0.Nonempty)
    (hB : ∀ H0 ∈ HF.holes, H0.card ≤ B)
    (hCq : ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)) < 1)
    (hAmp0 :
      0 ≤ C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
        g kScale ^ kappa0)
    (hA0 : 0 ≤ A)
    (hA : Real.exp s *
        (C * Hscale * Real.exp (-(c0 * (t0 : ℝ))) *
          g kScale ^ kappa0) ≤ A)
    (hsmall : A *
      (1 - ((3 ^ 4 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ 4 + 1)))⁻¹ ≤ 1) :
    let F : ∀ t k,
        BalabanCMP116LocalizedActivityFamily
          (Cube 4 L) lieDim (fun _ => Fin lieDim → ℝ)
            (OmegaPolymerType HF (z t k)) :=
      fun t k =>
        cmp116Lemma3LocalizedCubeActivityFamily
          (D t k) (physicalActivity t k) (Omega t k)
          (activeSupport t k)
          (activity_stronglyMeasurable t k)
          (spectatorSupport_subset t k)
          (fluctuationSupport_subset t k)
    let zK : Finset (Cube 4 L) → ℂ :=
      balabanCMP116AppendixFIntegratedKsharpActivityFamily
        HF z Λ F ν t0 kScale
    let zH : Finset (Cube 4 L) → ℂ := appendixFHoleHsharp HF zK
    KP.KPCriterion
      ((omegaHolePolymerSystem HF zH).scaleActivity (Real.exp s))
      (fun Y => (Y.val.card : ℝ)) := by
  let sourceMetric : ∀ t k, OmegaPolymerType HF (z t k) → ℕ :=
    fun t k X => cmp116CubeSourceTreeMetric (unionOf t k X)
  have hmetric :
      ∀ t k X, X ∈ Λ t k →
        (((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)) ≤
          (24 : ℝ) * ((sourceMetric t k X : ℝ) + 1) := by
    intro t k X hX
    simpa [sourceMetric] using
      discreteModifiedMetric_add_one_le_twentyFour_mul_cubeSourceTreeMetric_add_one
        HF X.val (unionOf t k X)
        X.property.1 X.property.2.1
        (hcarrier t k X hX)
        (hunion_nonempty t k X)
        (hunion_connected t k X)
  simpa [sourceMetric] using
    (cmp116Lemma3LocalizedCubeActivityFamily_KPCriterion_boundedHoles_of_scaledSourceMetric
      Λ D physicalActivity sourceMetric blockScale C3 epsilon1 delta
      kappaSource (fun _ _ => (24 : ℝ))
      B kappa0 Omega activeSupport activity_stronglyMeasurable
      spectatorSupport_subset fluctuationSupport_subset
      (by simpa [sourceMetric] using estimate)
      hmetric rate_margin ν g t0 kScale C Hscale c0 s A
      hkappa0 hν hamplitude_one hhalf hprofile amplitude_nonneg
      hdisj hnoedges hholes_ne hB hCq hAmp0 hA0 hA hsmall)

end

end YangMills.RG
