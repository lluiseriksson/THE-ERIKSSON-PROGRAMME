/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinCStarState

/-!
# Finite-set conditional kernels: the algebraic DLR layer

This file begins the finite-set, rather than merely single-site, DLR layer.
For a finite ambient spin system and a finite set `Lambda`, it defines the
exact conditional Gibbs kernel obtained by resampling all spins in `Lambda`
while holding its complement fixed.  Positivity, normalization, preservation
of constants, and dependence only on the exterior configuration are proved
directly from the positive weight.

The nested-set specification law and passage to the infinite-volume state are
deliberately not claimed until their finite-sum reindexing and limit arguments
are present below this layer.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical

section FiniteSetKernel

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype S] [Nonempty S]

/-- Replace precisely the coordinates in `Lambda` by the finite assignment
`x`, leaving every exterior coordinate equal to `eta`. -/
def patchFinset (Lambda : Finset ι) (eta : ι → S) (x : Lambda → S) : ι → S :=
  fun i => if hi : i ∈ Lambda then x ⟨i, hi⟩ else eta i

@[simp] theorem patchFinset_apply_mem (Lambda : Finset ι) (eta : ι → S)
    (x : Lambda → S) {i : ι} (hi : i ∈ Lambda) :
    patchFinset Lambda eta x i = x ⟨i, hi⟩ := by
  simp [patchFinset, hi]

@[simp] theorem patchFinset_apply_not_mem (Lambda : Finset ι) (eta : ι → S)
    (x : Lambda → S) {i : ι} (hi : i ∉ Lambda) :
    patchFinset Lambda eta x i = eta i := by
  simp [patchFinset, hi]

/-- The exact partition sum over assignments inside `Lambda`, with the
exterior configuration frozen. -/
noncomputable def finiteSetLocalZ (w : (ι → S) → ℝ) (Lambda : Finset ι)
    (eta : ι → S) : ℝ :=
  ∑ x : Lambda → S, w (patchFinset Lambda eta x)

theorem finiteSetLocalZ_pos {w : (ι → S) → ℝ} (hw : ∀ eta, 0 < w eta)
    (Lambda : Finset ι) (eta : ι → S) :
    0 < finiteSetLocalZ w Lambda eta := by
  unfold finiteSetLocalZ
  exact Finset.sum_pos (fun x _ => hw _) Finset.univ_nonempty

/-- Conditional probability of an interior assignment. -/
noncomputable def finiteSetGibbsKernel (w : (ι → S) → ℝ)
    (Lambda : Finset ι) (eta : ι → S) (x : Lambda → S) : ℝ :=
  w (patchFinset Lambda eta x) / finiteSetLocalZ w Lambda eta

theorem finiteSetGibbsKernel_pos {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι) (eta : ι → S)
    (x : Lambda → S) :
    0 < finiteSetGibbsKernel w Lambda eta x :=
  div_pos (hw _) (finiteSetLocalZ_pos hw Lambda eta)

theorem finiteSetGibbsKernel_nonneg {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι) (eta : ι → S)
    (x : Lambda → S) :
    0 ≤ finiteSetGibbsKernel w Lambda eta x :=
  (finiteSetGibbsKernel_pos hw Lambda eta x).le

theorem finiteSetGibbsKernel_sum_one {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι) (eta : ι → S) :
    ∑ x : Lambda → S, finiteSetGibbsKernel w Lambda eta x = 1 := by
  unfold finiteSetGibbsKernel finiteSetLocalZ
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (finiteSetLocalZ_pos hw Lambda eta))

/-- The finite-set conditional expectation operator. -/
noncomputable def finiteSetCondExp (w : (ι → S) → ℝ) (Lambda : Finset ι)
    (F : (ι → S) → ℝ) (eta : ι → S) : ℝ :=
  ∑ x : Lambda → S,
    finiteSetGibbsKernel w Lambda eta x * F (patchFinset Lambda eta x)

theorem finiteSetCondExp_one {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι) (eta : ι → S) :
    finiteSetCondExp w Lambda (fun _ => 1) eta = 1 := by
  unfold finiteSetCondExp
  simpa using finiteSetGibbsKernel_sum_one hw Lambda eta

theorem finiteSetCondExp_nonneg {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι)
    (F : (ι → S) → ℝ) (hF : ∀ eta, 0 ≤ F eta) (eta : ι → S) :
    0 ≤ finiteSetCondExp w Lambda F eta := by
  unfold finiteSetCondExp
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (finiteSetGibbsKernel_nonneg hw Lambda eta x) (hF _)

/-- If two boundary configurations agree off `Lambda`, the finite-set
conditional kernel is identical. -/
theorem finiteSetGibbsKernel_exterior
    (w : (ι → S) → ℝ) (Lambda : Finset ι) {eta eta' : ι → S}
    (h_ext : ∀ i, i ∉ Lambda → eta i = eta' i) :
    finiteSetGibbsKernel w Lambda eta =
      finiteSetGibbsKernel w Lambda eta' := by
  funext x
  have hpatch : patchFinset Lambda eta x = patchFinset Lambda eta' x := by
    funext i
    by_cases hi : i ∈ Lambda
    · simp [patchFinset, hi]
    · simp [patchFinset, hi, h_ext i hi]
  unfold finiteSetGibbsKernel finiteSetLocalZ
  rw [hpatch]
  congr 1
  exact Finset.sum_congr rfl fun y _ => by
    have hy : patchFinset Lambda eta y = patchFinset Lambda eta' y := by
      funext i
      by_cases hi : i ∈ Lambda
      · simp [patchFinset, hi]
      · simp [patchFinset, hi, h_ext i hi]
    rw [hy]

theorem finiteSetCondExp_exterior
    (w : (ι → S) → ℝ) (Lambda : Finset ι) (F : (ι → S) → ℝ)
    {eta eta' : ι → S} (h_ext : ∀ i, i ∉ Lambda → eta i = eta' i) :
    finiteSetCondExp w Lambda F eta = finiteSetCondExp w Lambda F eta' := by
  unfold finiteSetCondExp
  rw [finiteSetGibbsKernel_exterior w Lambda h_ext]
  apply Finset.sum_congr rfl
  intro x _
  have hpatch : patchFinset Lambda eta x = patchFinset Lambda eta' x := by
    funext i
    by_cases hi : i ∈ Lambda
    · simp [patchFinset, hi]
    · simp [patchFinset, hi, h_ext i hi]
  rw [hpatch]

/-- Resampling the same finite set twice changes nothing: the finite-set
conditional expectation is an idempotent Markov operator. -/
theorem finiteSetCondExp_idem {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι)
    (F : (ι → S) → ℝ) (eta : ι → S) :
    finiteSetCondExp w Lambda (finiteSetCondExp w Lambda F) eta =
      finiteSetCondExp w Lambda F eta := by
  unfold finiteSetCondExp
  calc
    ∑ x : Lambda → S,
        finiteSetGibbsKernel w Lambda eta x *
          finiteSetCondExp w Lambda F (patchFinset Lambda eta x) =
      ∑ x : Lambda → S,
        finiteSetGibbsKernel w Lambda eta x *
          finiteSetCondExp w Lambda F eta := by
        exact Finset.sum_congr rfl fun x _ => by
          rw [finiteSetCondExp_exterior w Lambda F
            (eta := patchFinset Lambda eta x) (eta' := eta)]
          intro i hi
          simp [patchFinset, hi]
    _ = finiteSetCondExp w Lambda F eta := by
      rw [← Finset.sum_mul, finiteSetGibbsKernel_sum_one hw, one_mul]

@[simp] theorem patchFinset_restrict_self (Lambda : Finset ι) (eta : ι → S) :
    patchFinset Lambda eta (fun i : Lambda => eta i) = eta := by
  funext i
  by_cases hi : i ∈ Lambda
  · simp [patchFinset, hi]
  · simp [patchFinset, hi]

theorem patchFinset_patch (Lambda : Finset ι) (eta : ι → S)
    (x y : Lambda → S) :
    patchFinset Lambda (patchFinset Lambda eta x) y =
      patchFinset Lambda eta y := by
  funext i
  by_cases hi : i ∈ Lambda
  · simp [patchFinset, hi]
  · simp [patchFinset, hi]

theorem finiteSetLocalZ_patch (w : (ι → S) → ℝ) (Lambda : Finset ι)
    (eta : ι → S) (x : Lambda → S) :
    finiteSetLocalZ w Lambda (patchFinset Lambda eta x) =
      finiteSetLocalZ w Lambda eta := by
  unfold finiteSetLocalZ
  exact Finset.sum_congr rfl fun y _ => by
    rw [patchFinset_patch]

/-- The simultaneous finite-set swap exchanges the old and new interior
assignments and is an involution. -/
def finiteSetSwap (Lambda : Finset ι) :
    ((ι → S) × (Lambda → S)) → ((ι → S) × (Lambda → S)) :=
  fun q => (patchFinset Lambda q.1 q.2, fun i => q.1 i)

theorem finiteSetSwap_involutive (Lambda : Finset ι) :
    Function.Involutive (finiteSetSwap (S := S) Lambda) := by
  intro q
  apply Prod.ext
  · funext i
    by_cases hi : i ∈ Lambda <;> simp [finiteSetSwap, patchFinset, hi]
  · funext i
    simp [finiteSetSwap, patchFinset]

/-- Exact finite-volume DLR/tower identity for every finite conditioning set.
It is proved by reindexing the double sum with `finiteSetSwap`; the desired
fixed-point equation is not an assumption. -/
theorem expect_finiteSetCondExp {w : (ι → S) → ℝ}
    (hw : ∀ eta, 0 < w eta) (Lambda : Finset ι)
    (F : (ι → S) → ℝ) :
    expect (gibbsMu w) (finiteSetCondExp w Lambda F) =
      expect (gibbsMu w) F := by
  unfold expect finiteSetCondExp
  have hL :
      ∑ eta, gibbsMu w eta *
          ∑ x : Lambda → S,
            finiteSetGibbsKernel w Lambda eta x *
              F (patchFinset Lambda eta x) =
        ∑ q : (ι → S) × (Lambda → S),
          gibbsMu w q.1 *
            (finiteSetGibbsKernel w Lambda q.1 q.2 *
              F (patchFinset Lambda q.1 q.2)) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun eta _ => by rw [Finset.mul_sum]
  rw [hL]
  have hswap :
      ∑ q : (ι → S) × (Lambda → S),
          gibbsMu w q.1 *
            (finiteSetGibbsKernel w Lambda q.1 q.2 *
              F (patchFinset Lambda q.1 q.2)) =
        ∑ q : (ι → S) × (Lambda → S),
          gibbsMu w (finiteSetSwap Lambda q).1 *
            (finiteSetGibbsKernel w Lambda
                (finiteSetSwap Lambda q).1 (finiteSetSwap Lambda q).2 *
              F (patchFinset Lambda (finiteSetSwap Lambda q).1
                (finiteSetSwap Lambda q).2)) := by
    exact (Equiv.sum_comp ((finiteSetSwap_involutive (S := S) Lambda).toPerm)
      (fun q : (ι → S) × (Lambda → S) =>
        gibbsMu w q.1 *
          (finiteSetGibbsKernel w Lambda q.1 q.2 *
            F (patchFinset Lambda q.1 q.2)))).symm
  rw [hswap]
  have hterm : ∀ q : (ι → S) × (Lambda → S),
      gibbsMu w (finiteSetSwap Lambda q).1 *
          (finiteSetGibbsKernel w Lambda
              (finiteSetSwap Lambda q).1 (finiteSetSwap Lambda q).2 *
            F (patchFinset Lambda (finiteSetSwap Lambda q).1
              (finiteSetSwap Lambda q).2)) =
        gibbsMu w (patchFinset Lambda q.1 q.2) *
          (w q.1 / finiteSetLocalZ w Lambda q.1 * F q.1) := by
    intro q
    unfold finiteSetSwap finiteSetGibbsKernel
    have hrestore :
        patchFinset Lambda (patchFinset Lambda q.1 q.2)
            (fun i : Lambda => q.1 i) = q.1 := by
      funext i
      by_cases hi : i ∈ Lambda <;> simp [patchFinset, hi]
    rw [hrestore, finiteSetLocalZ_patch]
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  rw [Fintype.sum_prod_type]
  have heta : ∀ eta : ι → S,
      ∑ x : Lambda → S,
          gibbsMu w (patchFinset Lambda eta x) *
            (w eta / finiteSetLocalZ w Lambda eta * F eta) =
        gibbsMu w eta * F eta := by
    intro eta
    have hfold :
        ∑ x : Lambda → S, gibbsMu w (patchFinset Lambda eta x) =
          finiteSetLocalZ w Lambda eta / gibbsZ w := by
      unfold gibbsMu finiteSetLocalZ
      rw [← Finset.sum_div]
    rw [← Finset.sum_mul, hfold]
    have hlz : finiteSetLocalZ w Lambda eta ≠ 0 :=
      ne_of_gt (finiteSetLocalZ_pos hw Lambda eta)
    have hZ : gibbsZ w ≠ 0 := ne_of_gt (gibbsZ_pos hw)
    unfold gibbsMu
    field_simp
  rw [Finset.sum_congr rfl fun eta _ => heta eta]

end FiniteSetKernel

end Dobrushin
end YangMills.OS
