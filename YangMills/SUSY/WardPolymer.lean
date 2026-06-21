/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.SUSY.WardComplex
import YangMills.RG.ClusterDecay

/-!
# Ward-cancelled polymer activities

This file connects the abstract Ward-cancellation layer to the existing
`Ω`-active with-holes cluster-tail consumer.

The mathematical content is deliberately conditional:

* a raw activity `H X` must be decomposed as `Q (B X) + R X`;
* the primitive/defect contribution and the cohomological remainder must obey
  the modified-metric profile;
* then the integrated activity `z(X) = expect (H X)` obeys the exact pointwise
  hypothesis consumed by `omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`.

Honest scope: this does not construct a supersymmetric Yang--Mills theory,
Grassmann/Berezin integration, a regulator, or the concrete decomposition of a
Yang--Mills fluctuation integral.  It is only the verified producer-to-consumer
bridge for such a future construction.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.SUSY

open scoped BigOperators
open YangMills.RG

attribute [local instance] Classical.propDecidable

/-! ## Finite algebraic Mayer transgression substrate -/

/-- Expanding a finite product after a base/defect split marks exactly the
subfamily `T` of factors where the defect is used.

This is the purely algebraic Mayer brick behind a future Ward transgression:
it does not assume exponentials, a derivation `Q`, integration, or any support
semantics beyond the finite index set. -/
theorem mayerProduct_decomp_eq_sum_powerset {ι R : Type*} [DecidableEq ι]
    [CommSemiring R] (S : Finset ι) (base defect : ι → R) :
    ∏ i ∈ S, (base i + defect i) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, defect i) * ∏ i ∈ S \ T, base i := by
  classical
  simpa [add_comm] using (Finset.prod_add defect base S)

/-- The non-base part of a finite Mayer product is a sum over nonempty
defect-marked subfamilies.  In the intended Ward use, these are the finite
sites at which a cohomological transgression has actually been spent. -/
theorem mayerProduct_sub_base_eq_sum_powerset_erase_empty {ι R : Type*}
    [DecidableEq ι] [CommRing R] (S : Finset ι) (base defect : ι → R) :
    (∏ i ∈ S, (base i + defect i)) - ∏ i ∈ S, base i =
      ∑ T ∈ S.powerset.erase (∅ : Finset ι),
        (∏ i ∈ T, defect i) * ∏ i ∈ S \ T, base i := by
  classical
  let term : Finset ι → R :=
    fun T => (∏ i ∈ T, defect i) * ∏ i ∈ S \ T, base i
  have hprod : ∏ i ∈ S, (base i + defect i) = ∑ T ∈ S.powerset, term T := by
    dsimp [term]
    simpa [add_comm] using (Finset.prod_add defect base S)
  have hmem_empty : (∅ : Finset ι) ∈ S.powerset := by
    simp
  have hempty : term (∅ : Finset ι) = ∏ i ∈ S, base i := by
    simp [term]
  calc
    (∏ i ∈ S, (base i + defect i)) - ∏ i ∈ S, base i
        = (∑ T ∈ S.powerset, term T) - ∏ i ∈ S, base i := by
          rw [hprod]
    _ = (∑ T ∈ S.powerset.erase (∅ : Finset ι), term T
            + term (∅ : Finset ι)) - ∏ i ∈ S, base i := by
          rw [Finset.sum_erase_add S.powerset term hmem_empty]
    _ = ∑ T ∈ S.powerset.erase (∅ : Finset ι), term T := by
          rw [hempty]
          ring

/-- Membership in the defect-marked part of the product expansion is exactly
"a nonempty subfamily of the original finite family". -/
theorem mem_mayerProduct_defectSubsets_iff {ι : Type*} [DecidableEq ι]
    {S T : Finset ι} :
    T ∈ S.powerset.erase (∅ : Finset ι) ↔ T ⊆ S ∧ T.Nonempty := by
  classical
  simp [Finset.mem_powerset, Finset.nonempty_iff_ne_empty, and_comm]

/-- Defect-marked subfamilies cannot create new support: their support union is
contained in the support union of the original Mayer family.  This is the finite
support-preservation guard needed before any analytic Ward or BV semantics are
added later. -/
theorem mayerProduct_defectSupport_subset {ι Site : Type*}
    [DecidableEq ι] [DecidableEq Site] (S T : Finset ι)
    (support : ι → Finset Site)
    (hT : T ∈ S.powerset.erase (∅ : Finset ι)) :
    T.biUnion support ⊆ S.biUnion support := by
  intro x hx
  rw [Finset.mem_biUnion] at hx ⊢
  rcases hx with ⟨i, hiT, hxi⟩
  exact ⟨i, (mem_mayerProduct_defectSubsets_iff.mp hT).1 hiT, hxi⟩

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A finite-scale version of the Ward-defect estimate.  The norm of a finite
sum of `Q`-exact expectations is bounded by the sum of the individual defects. -/
theorem norm_finset_sum_expect_Q_le {ι : Type*} (S : Finset ι)
    (W : ι → ApproxWardComplex A) (B : ι → A) :
    ‖∑ k ∈ S, (W k).expect ((W k).Q (B k))‖
      ≤ ∑ k ∈ S, (W k).defect * ‖B k‖ := by
  calc
    ‖∑ k ∈ S, (W k).expect ((W k).Q (B k))‖
        ≤ ∑ k ∈ S, ‖(W k).expect ((W k).Q (B k))‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ k ∈ S, (W k).defect * ‖B k‖ := by
      exact Finset.sum_le_sum fun k _ => (W k).ward_bound (B k)

/-- The integrated complex polymer activity produced by a Ward complex. -/
noncomputable def wardActivity {d L : ℕ} (W : ApproxWardComplex A)
    (Hraw : Finset (Cube d L) → A) : Finset (Cube d L) → ℂ :=
  fun X => W.expect (Hraw X)

/-- Pointwise modified-metric activity bound from a Ward decomposition, when the
combined defect/remainder profile is already provided in the tilted form
consumed by the RG cluster-tail machinery. -/
theorem wardActivity_metric_bound_of_decomposition {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (W : ApproxWardComplex A)
    (Hraw B R : Finset (Cube d L) → A)
    (t q Aamp : ℝ)
    (hdec : ∀ X, Hraw X = W.Q (B X) + R X)
    (hprofile : ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t *
          (W.defect * ‖B c.val‖ + ‖W.expect (R c.val)‖) *
          Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1)) :
    ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t *
          ‖(omegaHolePolymerSystem HF (wardActivity W Hraw)).activity c‖ *
          Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1) := by
  intro c
  have hward :=
    expect_decomposition_bound W (Hraw c.val) (B c.val) (R c.val) (hdec c.val)
  have hmul :
      Real.exp t * ‖(omegaHolePolymerSystem HF (wardActivity W Hraw)).activity c‖ *
          Real.exp (c.val.card : ℝ)
        ≤
      Real.exp t * (W.defect * ‖B c.val‖ + ‖W.expect (R c.val)‖) *
          Real.exp (c.val.card : ℝ) := by
    dsimp [wardActivity, omegaHolePolymerSystem]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hward (Real.exp_nonneg t))
      (Real.exp_nonneg _)
  exact hmul.trans (hprofile c)

/-- Pointwise modified-metric activity bound in the exact Ward case: the
`Q`-exact sector disappears before norms are applied. -/
theorem wardActivity_metric_bound_of_exact {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (W : ApproxWardComplex A)
    (Hraw B R : Finset (Cube d L) → A)
    (t q Aamp : ℝ)
    (hdefect : W.defect = 0)
    (hdec : ∀ X, Hraw X = W.Q (B X) + R X)
    (hRprofile : ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t * ‖W.expect (R c.val)‖ * Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1)) :
    ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t *
          ‖(omegaHolePolymerSystem HF (wardActivity W Hraw)).activity c‖ *
          Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1) := by
  intro c
  have heq :=
    expect_eq_expect_remainder_of_defect_eq_zero W hdefect
      (Hraw c.val) (B c.val) (R c.val) (hdec c.val)
  dsimp [wardActivity, omegaHolePolymerSystem]
  rw [heq]
  exact hRprofile c

/-- Final approximate-Ward consumer for the existing `Ω`-active skeleton
cluster-tail theorem.  All genuinely model-specific work remains in the
decomposition and profile hypotheses. -/
theorem omegaClusterSkeletonRemainderSum_tsum_le_of_ward
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (W : ApproxWardComplex A)
    (Hraw B R : Finset (Cube d L) → A)
    (r : Cube d L) (t q Aamp : ℝ) (ht : 0 < t)
    (hA0 : 0 ≤ Aamp)
    (hdec : ∀ X, Hraw X = W.Q (B X) + R X)
    (hprofile : ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t *
          (W.defect * ‖B c.val‖ + ‖W.expect (R c.val)‖) *
          Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall : Aamp *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    ∑' n, omegaClusterSkeletonRemainderSumTerm HF (wardActivity W Hraw) r n
      ≤ t⁻¹ * (Aamp *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹) :=
  omegaClusterSkeletonRemainderSum_tsum_le_metric_bound HF
    (wardActivity W Hraw) r t q Aamp ht hA0
    (wardActivity_metric_bound_of_decomposition HF W Hraw B R t q Aamp hdec hprofile)
    hdisj hnoedges hholes_ne hq0 hCq hsmall

/-- Final exact-Ward consumer: only the cohomological remainder profile enters
the existing `Ω`-active skeleton cluster-tail theorem. -/
theorem omegaClusterSkeletonRemainderSum_tsum_le_of_exact_ward
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (W : ApproxWardComplex A)
    (Hraw B R : Finset (Cube d L) → A)
    (r : Cube d L) (t q Aamp : ℝ) (ht : 0 < t)
    (hA0 : 0 ≤ Aamp)
    (hdefect : W.defect = 0)
    (hdec : ∀ X, Hraw X = W.Q (B X) + R X)
    (hRprofile : ∀ c : OmegaPolymerType HF (wardActivity W Hraw),
      Real.exp t * ‖W.expect (R c.val)‖ * Real.exp (c.val.card : ℝ)
        ≤ Aamp * q ^ (discreteModifiedMetric HF c.val + 1))
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hq0 : 0 ≤ q)
    (hCq : ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)) < 1)
    (hsmall : Aamp *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹ ≤ 1) :
    ∑' n, omegaClusterSkeletonRemainderSumTerm HF (wardActivity W Hraw) r n
      ≤ t⁻¹ * (Aamp *
        (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 * (q * 2 ^ (3 ^ d + 1)))⁻¹) :=
  omegaClusterSkeletonRemainderSum_tsum_le_metric_bound HF
    (wardActivity W Hraw) r t q Aamp ht hA0
    (wardActivity_metric_bound_of_exact HF W Hraw B R t q Aamp
      hdefect hdec hRprofile)
    hdisj hnoedges hholes_ne hq0 hCq hsmall

end YangMills.SUSY
