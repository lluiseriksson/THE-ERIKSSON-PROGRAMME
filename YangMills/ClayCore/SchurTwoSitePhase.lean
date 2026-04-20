/-
  YangMills/ClayCore/SchurTwoSitePhase.lean

  Two-site phase element of SU(N): diag(I at i, -I at j, 1 elsewhere).
  Used in L2.5 to force off-diagonal terms in ∫ |tr U|² dHaar to vanish:
  left-multiplication flips the sign of U_{ii}·conj(U_{jj}).

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/
import YangMills.ClayCore.SchurZeroMean

noncomputable section
open Matrix Complex
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ}

/-! ### Diagonal vector with two phase entries -/

/-- Diagonal vector: `I` at position `i`, `-I` at `j`, `1` elsewhere. -/
def twoSiteVec (i j : Fin N) : Fin N → ℂ := fun k =>
  if k = i then Complex.I else if k = j then -Complex.I else 1

@[simp] lemma twoSiteVec_at_i (i j : Fin N) : twoSiteVec i j i = Complex.I := by
  simp [twoSiteVec]

lemma twoSiteVec_at_j {i j : Fin N} (h : i ≠ j) :
    twoSiteVec i j j = -Complex.I := by
  unfold twoSiteVec
  rw [if_neg h.symm, if_pos rfl]

lemma twoSiteVec_at_other {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j) :
    twoSiteVec i j k = 1 := by
  unfold twoSiteVec
  rw [if_neg hki, if_neg hkj]

private lemma star_I_eq : star (Complex.I) = -Complex.I := by
  show (starRingEnd ℂ) Complex.I = -Complex.I
  exact Complex.conj_I

private lemma star_neg_I_eq : star (-Complex.I : ℂ) = Complex.I := by
  rw [star_neg, star_I_eq, neg_neg]

/-- Each entry of `twoSiteVec` has unit modulus. -/
lemma twoSiteVec_mul_star (i j k : Fin N) :
    twoSiteVec i j k * star (twoSiteVec i j k) = 1 := by
  unfold twoSiteVec
  by_cases h1 : k = i
  · rw [if_pos h1, star_I_eq, mul_neg, Complex.I_mul_I]; ring
  · rw [if_neg h1]
    by_cases h2 : k = j
    · rw [if_pos h2, star_neg_I_eq, neg_mul, Complex.I_mul_I]; ring
    · rw [if_neg h2]; simp

/-- The product of all entries of `twoSiteVec i j` is `1` (since `I · (-I) = 1`). -/
lemma twoSiteVec_prod_eq_one {i j : Fin N} (hij : i ≠ j) :
    (∏ k, twoSiteVec i j k) = 1 := by
  have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have hrest : ∀ x ∈ (Finset.univ : Finset (Fin N)),
      x ∉ ({i, j} : Finset (Fin N)) → twoSiteVec i j x = 1 := by
    intro x _ hx
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact twoSiteVec_at_other hx.1 hx.2
  rw [← Finset.prod_subset hsub hrest,
      Finset.prod_insert (by simp [hij]),
      Finset.prod_singleton,
      twoSiteVec_at_i, twoSiteVec_at_j hij,
      mul_neg, Complex.I_mul_I]
  ring

/-! ### Two-site phase as a matrix and as an element of SU(N) -/

/-- Two-site phase matrix: `diagonal(twoSiteVec i j)`. -/
def twoSitePhase (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (twoSiteVec i j)

lemma twoSitePhase_det {i j : Fin N} (hij : i ≠ j) :
    (twoSitePhase i j).det = 1 := by
  unfold twoSitePhase
  rw [Matrix.det_diagonal]
  exact twoSiteVec_prod_eq_one hij

lemma twoSitePhase_mul_conjTranspose (i j : Fin N) :
    twoSitePhase i j * (twoSitePhase i j).conjTranspose = 1 := by
  unfold twoSitePhase
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hfun :
      (fun k => twoSiteVec i j k * (star (twoSiteVec i j)) k)
        = fun _ : Fin N => (1 : ℂ) := by
    funext k
    exact twoSiteVec_mul_star i j k
  rw [hfun]
  exact Matrix.diagonal_one

/-- Two-site phase, promoted to `SU(N)`. Requires `i ≠ j`. -/
def twoSiteSU (i j : Fin N) (hij : i ≠ j) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ⟨twoSitePhase i j, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, twoSitePhase_det hij⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact twoSitePhase_mul_conjTranspose i j⟩

@[simp] lemma twoSiteSU_val (i j : Fin N) (hij : i ≠ j) :
    (twoSiteSU i j hij).val = twoSitePhase i j := rfl

/-! ### Action on the k-th diagonal entry -/

/-- Left-multiplication by the two-site phase scales the `k`-th diagonal entry
    of `U` by `twoSiteVec i j k` (which is `I`, `-I`, or `1`). -/
lemma twoSiteSU_apply_diag (i j : Fin N) (hij : i ≠ j)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (k : Fin N) :
    ((twoSiteSU i j hij * U).val) k k = twoSiteVec i j k * U.val k k := by
  have hmul : ((twoSiteSU i j hij * U).val : Matrix (Fin N) (Fin N) ℂ)
      = (twoSiteSU i j hij).val * U.val := rfl
  rw [hmul, twoSiteSU_val]
  show (twoSitePhase i j * U.val) k k = twoSiteVec i j k * U.val k k
  unfold twoSitePhase
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hbk
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hbk)]; ring
  · intro h
    exact absurd (Finset.mem_univ k) h

end YangMills.ClayCore

end