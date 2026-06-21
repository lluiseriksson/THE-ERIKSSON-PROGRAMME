import YangMills.RG.AppendixFLocalSummability
import YangMills.RG.HolePolymerSystem

/-!
# Appendix F cluster3 source geometry

This module packages the source-facing geometry needed by the direct
Dimock-II Appendix F route.  It deliberately stays finite and purely
geometric: holes, the active region `Ω`, skeletons, and a local
incompatibility estimate whose analytic input is only a rooted summability
bound.

The intended later use is that a source theorem, such as Dimock-II cluster3,
can discharge the rooted summability hypothesis without changing downstream
Appendix-F consumers.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills
namespace RG

open Finset
open scoped BigOperators

namespace HoleFamily

/-- The finite union of all hole components. -/
def holeRegion {d L : ℕ} (HF : HoleFamily d L) : Finset (Cube d L) :=
  HF.holes.biUnion id

/-- The active finite region `Ω`, obtained by removing the holes. -/
def omegaRegion {d L : ℕ} [NeZero L] (HF : HoleFamily d L) : Finset (Cube d L) :=
  (Finset.univ : Finset (Cube d L)) \ HF.holeRegion

end HoleFamily

/-- The skeleton is exactly the intersection with the active region `Ω`. -/
@[simp]
theorem skeleton_eq_inter_omegaRegion {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (X : Finset (Cube d L)) :
    skeleton HF X = X ∩ HF.omegaRegion := by
  classical
  ext x
  simp [skeleton, HoleFamily.omegaRegion, HoleFamily.holeRegion]

/--
Finite hole geometry assumed by a source-level cluster3 theorem.

This is a packaging structure only: the local estimates below use the pieces
they need directly, while later source adapters can carry this as the typed
record corresponding to the Dimock-II hypotheses on holes.
-/
structure AppendixFCluster3HoleGeometry {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) : Prop where
  holes_nonempty : ∀ H ∈ HF.holes, H.Nonempty
  holes_connected : ∀ H ∈ HF.holes, cubeConnected H
  holes_pairwise_disjoint :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂
  no_edges_between_holes :
    noEdgesBetweenHoles (cubeAdj d L) HF.holes

/--
Local finite incompatibility estimate from a rooted summability hypothesis.

If every root cube has total exponential weight at most `K₀`, then the total
weight of polymers incompatible with `P` is bounded by the modified metric
size of `P` times `K₀`.  This is the source-facing form wanted for the
direct cluster3 route: the later analytic source result only has to prove
`hroot`.
-/
theorem appendixFHole_incompatibleExpWeightSum_le_metric_mul_of_rooted
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (κ₀ K₀ : ℝ)
    (hK₀ : 0 ≤ K₀)
    (hroot :
      ∀ r : Cube d L,
        (∑ Q ∈
            (Finset.univ :
              Finset (OmegaPolymerType HF zK)).filter
                (fun Q => r ∈ skeleton HF Q.val),
          appendixFHoleExpWeight HF κ₀ Q.val) ≤ K₀)
    (P : OmegaPolymerType HF zK) :
    (∑ Q ∈
        (Finset.univ :
          Finset (OmegaPolymerType HF zK)).filter
            (fun Q =>
              (omegaHolePolymerSystem HF zK).incomp P Q),
      appendixFHoleExpWeight HF κ₀ Q.val)
      ≤
    (((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)) * K₀ := by
  classical
  let w : OmegaPolymerType HF zK → ℝ :=
    fun Q => appendixFHoleExpWeight HF κ₀ Q.val
  let incompFiber : Finset (OmegaPolymerType HF zK) :=
    (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
      (fun Q => (omegaHolePolymerSystem HF zK).incomp P Q)
  let rootFiber : Cube d L → Finset (OmegaPolymerType HF zK) :=
    fun r =>
      (Finset.univ : Finset (OmegaPolymerType HF zK)).filter
        (fun Q => r ∈ skeleton HF Q.val)
  have hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q := by
    intro Q
    exact appendixFHoleExpWeight_nonneg HF κ₀ Q.val
  have hsub : incompFiber ⊆ (skeleton HF P.val).biUnion rootFiber := by
    intro Q hQ
    dsimp [incompFiber] at hQ
    rw [Finset.mem_filter] at hQ
    rcases (omegaHolePolymerSystem_incomp_iff_exists HF zK P Q).mp hQ.2 with
      ⟨r, hrP, hrQ⟩
    dsimp [rootFiber]
    rw [Finset.mem_biUnion]
    exact ⟨r, hrP, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ Q, hrQ⟩⟩
  have hsubset_sum :
      (∑ Q ∈ incompFiber, w Q) ≤
        ∑ Q ∈ (skeleton HF P.val).biUnion rootFiber, w Q := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro Q _hQ hQnot
      exact hw Q)
  have hbiUnion :
      (∑ Q ∈ (skeleton HF P.val).biUnion rootFiber, w Q) ≤
        ∑ r ∈ skeleton HF P.val, ∑ Q ∈ rootFiber r, w Q :=
    sum_biUnion_le (skeleton HF P.val) rootFiber w hw
  have hroot_sum :
      (∑ r ∈ skeleton HF P.val, ∑ Q ∈ rootFiber r, w Q) ≤
        ∑ _r ∈ skeleton HF P.val, K₀ := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    simpa [rootFiber, w] using hroot r
  have hconst :
      (∑ _r ∈ skeleton HF P.val, K₀) =
        ((skeleton HF P.val).card : ℝ) * K₀ := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat :
      (skeleton HF P.val).card ≤ discreteModifiedMetric HF P.val + 1 :=
    skeleton_card_le_discreteModifiedMetric_add_one HF P.val P.property.right.left
  have hcard :
      ((skeleton HF P.val).card : ℝ) ≤
        (((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hcard_nat
  calc
    (∑ Q ∈
        (Finset.univ :
          Finset (OmegaPolymerType HF zK)).filter
            (fun Q =>
              (omegaHolePolymerSystem HF zK).incomp P Q),
      appendixFHoleExpWeight HF κ₀ Q.val)
        = ∑ Q ∈ incompFiber, w Q := by
            simp [incompFiber, w]
    _ ≤ ∑ Q ∈ (skeleton HF P.val).biUnion rootFiber, w Q := hsubset_sum
    _ ≤ ∑ r ∈ skeleton HF P.val, ∑ Q ∈ rootFiber r, w Q := hbiUnion
    _ ≤ ∑ _r ∈ skeleton HF P.val, K₀ := hroot_sum
    _ = ((skeleton HF P.val).card : ℝ) * K₀ := hconst
    _ ≤ (((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)) * K₀ :=
        mul_le_mul_of_nonneg_right hcard hK₀

end RG
end YangMills
