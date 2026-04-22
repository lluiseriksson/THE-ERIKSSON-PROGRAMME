/-
  YangMills/ClayCore/SchurEntryDiagonal.lean
  (Rounds 1–3: the main integral theorem `∫|U_{ij}|² dHaar = 1/N` on SU(N).)

  * Round 1: pair-rotation matrix + unitarity
      `rotPairMat i j * star (rotPairMat i j) = 1`
  * Round 2: determinant = 1 + SU(N) packaging
      `det (rotPairMat i j) = 1` and `rotPairSU hij : specialUnitaryGroup`
  * Round 3: ∫ |U_{ij}|² = 1/N
      via row-squared-sum identity from unitarity + column symmetry from
      right-invariance of Haar under right-multiplication by `rotPairSU`.

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Group.Integral
import YangMills.ClayCore.SchurZeroMean

noncomputable section
open Matrix Complex MeasureTheory
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ}

/-- Quarter-rotation on the (i,j)-block: `[[0,-1],[1,0]]`, identity elsewhere. -/
def rotPairMat (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun r c =>
    if r = i then (if c = j then (-1 : ℂ) else 0)
    else if r = j then (if c = i then (1 : ℂ) else 0)
    else if r = c then (1 : ℂ)
    else (0 : ℂ)

/-! ### Entry-wise evaluation -/

lemma rotPairMat_apply_i (i j : Fin N) (c : Fin N) :
    rotPairMat i j i c = if c = j then (-1 : ℂ) else 0 := by
  unfold rotPairMat
  rw [Matrix.of_apply, if_pos rfl]

lemma rotPairMat_apply_j {i j : Fin N} (hij : i ≠ j) (c : Fin N) :
    rotPairMat i j j c = if c = i then (1 : ℂ) else 0 := by
  unfold rotPairMat
  rw [Matrix.of_apply, if_neg (Ne.symm hij), if_pos rfl]

lemma rotPairMat_apply_other {i j : Fin N} {r : Fin N}
    (hri : r ≠ i) (hrj : r ≠ j) (c : Fin N) :
    rotPairMat i j r c = if r = c then (1 : ℂ) else 0 := by
  unfold rotPairMat
  rw [Matrix.of_apply, if_neg hri, if_neg hrj]

/-! ### Row sums: each row has a single nonzero column -/

lemma rotPairMat_row_i_sum (i j : Fin N) (f : Fin N → ℂ) :
    ∑ k, rotPairMat i j i k * f k = -(f j) := by
  have hsum : ∑ k, rotPairMat i j i k * f k = rotPairMat i j i j * f j := by
    apply Finset.sum_eq_single
    · intro k _ hk
      rw [rotPairMat_apply_i, if_neg hk]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hsum, rotPairMat_apply_i, if_pos rfl]; ring

lemma rotPairMat_row_j_sum {i j : Fin N} (hij : i ≠ j) (f : Fin N → ℂ) :
    ∑ k, rotPairMat i j j k * f k = f i := by
  have hsum : ∑ k, rotPairMat i j j k * f k = rotPairMat i j j i * f i := by
    apply Finset.sum_eq_single
    · intro k _ hk
      rw [rotPairMat_apply_j hij, if_neg hk]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsum, rotPairMat_apply_j hij, if_pos rfl]; ring

lemma rotPairMat_row_other_sum {i j : Fin N} {r : Fin N}
    (hri : r ≠ i) (hrj : r ≠ j) (f : Fin N → ℂ) :
    ∑ k, rotPairMat i j r k * f k = f r := by
  have hsum : ∑ k, rotPairMat i j r k * f k = rotPairMat i j r r * f r := by
    apply Finset.sum_eq_single
    · intro k _ hk
      rw [rotPairMat_apply_other hri hrj, if_neg (Ne.symm hk)]; ring
    · intro h; exact absurd (Finset.mem_univ r) h
  rw [hsum, rotPairMat_apply_other hri hrj, if_pos rfl]; ring

/-! ### Round 1: unitarity `rotPairMat i j * star (rotPairMat i j) = 1` -/

lemma rotPairMat_mul_star_eq_one {i j : Fin N} (hij : i ≠ j) :
    rotPairMat i j * star (rotPairMat i j) = 1 := by
  have hji : j ≠ i := Ne.symm hij
  ext r c
  rw [Matrix.mul_apply, Matrix.one_apply]
  change ∑ k, rotPairMat i j r k * star (rotPairMat i j c k) = _
  by_cases hri : r = i
  · rw [hri, rotPairMat_row_i_sum i j (fun k => star (rotPairMat i j c k))]
    by_cases hic : i = c
    · rw [← hic, rotPairMat_apply_i]; simp
    · rw [if_neg hic]
      by_cases hcj : c = j
      · rw [hcj, rotPairMat_apply_j hij, if_neg hji]; simp
      · have hci : c ≠ i := fun h => hic h.symm
        rw [rotPairMat_apply_other hci hcj, if_neg hcj]; simp
  · by_cases hrj : r = j
    · rw [hrj, rotPairMat_row_j_sum hij (fun k => star (rotPairMat i j c k))]
      by_cases hjc : j = c
      · rw [← hjc, rotPairMat_apply_j hij]; simp
      · rw [if_neg hjc]
        by_cases hci : c = i
        · rw [hci, rotPairMat_apply_i, if_neg hij]; simp
        · have hcj : c ≠ j := fun h => hjc h.symm
          rw [rotPairMat_apply_other hci hcj, if_neg hci]; simp
    · rw [rotPairMat_row_other_sum hri hrj (fun k => star (rotPairMat i j c k))]
      by_cases hrc : r = c
      · rw [← hrc, rotPairMat_apply_other hri hrj]; simp
      · rw [if_neg hrc]
        by_cases hci : c = i
        · rw [hci, rotPairMat_apply_i, if_neg hrj]; simp
        · by_cases hcj : c = j
          · rw [hcj, rotPairMat_apply_j hij, if_neg hri]; simp
          · rw [rotPairMat_apply_other hci hcj, if_neg (fun h => hrc h.symm)]; simp

/-! ### Round 2: determinant `det (rotPairMat i j) = 1` -/

private def rotDiagVec (i : Fin N) : Fin N → ℂ :=
  fun k => if k = i then (-1 : ℂ) else 1

private lemma rotDiagVec_at_i (i : Fin N) : rotDiagVec i i = -1 := by
  unfold rotDiagVec; rw [if_pos rfl]

private lemma rotDiagVec_at_ne (i : Fin N) {k : Fin N} (h : k ≠ i) : rotDiagVec i k = 1 := by
  unfold rotDiagVec; rw [if_neg h]

private lemma rotDiagVec_prod (i : Fin N) : ∏ k, rotDiagVec i k = (-1 : ℂ) := by
  have h : ∏ k, rotDiagVec i k = rotDiagVec i i := by
    apply Finset.prod_eq_single i
    · intro k _ hki; exact rotDiagVec_at_ne i hki
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h, rotDiagVec_at_i]

private lemma permMatrix_swap_apply (i j r c : Fin N) :
    ((Equiv.swap i j).permMatrix ℂ) r c = if Equiv.swap i j r = c then (1 : ℂ) else 0 := by
  show ((Equiv.swap i j).toPEquiv.toMatrix : Matrix (Fin N) (Fin N) ℂ) r c = _
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp [Option.mem_def]

lemma rotPairMat_eq_diag_mul_perm {i j : Fin N} (hij : i ≠ j) :
    rotPairMat i j = Matrix.diagonal (rotDiagVec i) * (Equiv.swap i j).permMatrix ℂ := by
  have hji : j ≠ i := Ne.symm hij
  ext r c
  rw [Matrix.mul_apply]
  have hsingle :
      (∑ k, Matrix.diagonal (rotDiagVec i) r k * ((Equiv.swap i j).permMatrix ℂ) k c)
        = rotDiagVec i r * ((Equiv.swap i j).permMatrix ℂ) r c := by
    rw [Finset.sum_eq_single r]
    · rw [Matrix.diagonal_apply_eq]
    · intro b _ hbr
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hbr)]; ring
    · intro h; exact absurd (Finset.mem_univ r) h
  rw [hsingle, permMatrix_swap_apply]
  by_cases hri : r = i
  · rw [hri, rotPairMat_apply_i, rotDiagVec_at_i, Equiv.swap_apply_left]
    by_cases hcj : c = j
    · rw [if_pos hcj, if_pos hcj.symm]; ring
    · rw [if_neg hcj, if_neg (fun h => hcj h.symm)]; ring
  · by_cases hrj : r = j
    · rw [hrj, rotPairMat_apply_j hij, rotDiagVec_at_ne i hji, Equiv.swap_apply_right]
      by_cases hci : c = i
      · rw [if_pos hci, if_pos hci.symm]; ring
      · rw [if_neg hci, if_neg (fun h => hci h.symm)]; ring
    · rw [rotPairMat_apply_other hri hrj, rotDiagVec_at_ne i hri,
          Equiv.swap_apply_of_ne_of_ne hri hrj, one_mul]

lemma rotPairMat_det {i j : Fin N} (hij : i ≠ j) : (rotPairMat i j).det = 1 := by
  rw [rotPairMat_eq_diag_mul_perm hij,
      Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation,
      rotDiagVec_prod, Equiv.Perm.sign_swap hij]
  simp

/-- Rotation-pair matrix packaged as an element of SU(N). -/
def rotPairSU {i j : Fin N} (hij : i ≠ j) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ⟨rotPairMat i j, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, rotPairMat_det hij⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact rotPairMat_mul_star_eq_one hij⟩

@[simp] lemma rotPairSU_val {i j : Fin N} (hij : i ≠ j) :
    (rotPairSU hij).val = rotPairMat i j := rfl

/-! ### Round 3: the main integral theorem

  `∫ |U_{ij}|² dHaar = 1/N` on `SU(N)`.

  Strategy:
    (1) Row squared-sum identity from unitarity: `∑ k, U_{ik} · star U_{ik} = 1`.
    (2) Integrate: `∑ k, ∫ |U_{ik}|² = 1`.
    (3) Column symmetry via right-multiplication by `rotPairSU` together with
        right-invariance of Haar: `∫ |U_{ij}|² = ∫ |U_{ij'}|²` for `j ≠ j'`.
    (4) Combine: all `N` integrals are equal and sum to `1`, so each is `1/N`. -/

variable [NeZero N]

/-- Right-multiplication by `rotPairSU hij` sends column `j` of `U` into column `i`. -/
lemma rotPairSU_apply_col_i {i j : Fin N} (hij : i ≠ j) (r : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (U * rotPairSU hij).val r i = U.val r j := by
  have hval : (U * rotPairSU hij).val = U.val * rotPairMat i j := rfl
  rw [hval, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [rotPairMat_apply_j hij, if_pos rfl, mul_one]
  · intro k _ hkj
    by_cases hki : k = i
    · rw [hki, rotPairMat_apply_i, if_neg hij]; ring
    · rw [rotPairMat_apply_other hki hkj, if_neg hki]; ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Continuity of each matrix entry as a function on `SU(N)`. -/
private lemma continuous_su_entry (i j : Fin N) :
    Continuous (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ => U.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- `U ↦ U_{ij} · star U_{ij}` is integrable against the Haar measure. -/
lemma entry_normSq_integrable (i j : Fin N) :
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      U.val i j * star (U.val i j)) (sunHaarProb N) :=
  ((continuous_su_entry i j).mul
    (continuous_star.comp (continuous_su_entry i j))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Row-squared-sum identity from unitarity: `∑ k, U_{ik} · star U_{ik} = 1`. -/
lemma row_normSq_sum_eq_one (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (i : Fin N) :
    ∑ k : Fin N, U.val i k * star (U.val i k) = 1 := by
  have hU_unit : U.val ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have hUstar : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.mp hU_unit
  have hii : (U.val * star U.val) i i = (1 : Matrix (Fin N) (Fin N) ℂ) i i := by
    rw [hUstar]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii
  rw [← hii]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.star_apply]

/-- Integrated row-squared-sum: `∑ k, ∫ |U_{ik}|² = 1`. -/
lemma row_integral_normSq_sum_eq_one (i : Fin N) :
    ∑ k : Fin N, (∫ U, U.val i k * star (U.val i k) ∂(sunHaarProb N)) = 1 := by
  rw [← integral_finset_sum Finset.univ
      (fun k _ => entry_normSq_integrable i k)]
  have heq : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      (∑ k : Fin N, U.val i k * star (U.val i k)) = 1 :=
    fun U => row_normSq_sum_eq_one U i
  simp_rw [heq]
  rw [MeasureTheory.integral_const]
  first
    | (simp; done)
    | (simp; exact one_smul ℝ (1 : ℂ))
    | (simp only [measureReal_univ_eq_one]; exact one_smul ℝ (1 : ℂ))
    | (simp only [measure_univ, ENNReal.toReal_one]; exact one_smul ℝ (1 : ℂ))

/-- Column symmetry: `∫ |U_{rj}|² = ∫ |U_{ri}|²` for `i ≠ j`. -/
lemma entry_normSq_col_symm {i j : Fin N} (hij : i ≠ j) (r : Fin N) :
    (∫ U, U.val r j * star (U.val r j) ∂(sunHaarProb N))
      = ∫ U, U.val r i * star (U.val r i) ∂(sunHaarProb N) := by
  haveI hinv : (sunHaarProb N).IsMulRightInvariant := sunHaarProb_isMulRightInvariant N
  have hshift :
    (∫ U, (U * rotPairSU hij).val r i * star ((U * rotPairSU hij).val r i) ∂(sunHaarProb N))
      = ∫ U, U.val r i * star (U.val r i) ∂(sunHaarProb N) :=
    integral_mul_right_eq_self
      (fun U => U.val r i * star (U.val r i)) (rotPairSU hij)
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show U.val r j * star (U.val r j)
      = (U * rotPairSU hij).val r i * star ((U * rotPairSU hij).val r i)
  rw [rotPairSU_apply_col_i hij r U]

/-- **Main theorem.** `∫ U_{ij} · star U_{ij} dHaar = 1/N` on `SU(N)`. -/
theorem sunHaarProb_entry_normSq_eq_inv_N (i j : Fin N) :
    (∫ U, U.val i j * star (U.val i j) ∂(sunHaarProb N)) = 1 / (N : ℂ) := by
  have hall_eq : ∀ k : Fin N,
      (∫ U, U.val i k * star (U.val i k) ∂(sunHaarProb N))
        = ∫ U, U.val i j * star (U.val i j) ∂(sunHaarProb N) := fun k => by
    by_cases hkj : k = j
    · rw [hkj]
    · exact (entry_normSq_col_symm hkj i).symm
  have hsum := row_integral_normSq_sum_eq_one i
  simp_rw [hall_eq] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [eq_div_iff hN_ne, mul_comm]
  exact hsum

end YangMills.ClayCore

end
