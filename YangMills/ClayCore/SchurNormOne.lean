import Mathlib
import YangMills.ClayCore.SchurEntryOffDiag
import YangMills.ClayCore.SchurL25
import YangMills.P8_PhysicalGap.SUN_StateConstruction

noncomputable section

open Matrix Complex MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators NNReal ENNReal

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

/-- Signed permutation matrix swapping i and j. -/
def signedSwapMat (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if a = i ∧ b = j then -1
  else if a = j ∧ b = i then 1
  else if a = b ∧ a ≠ i ∧ a ≠ j then 1
  else 0

lemma signedSwapMat_apply (i j : Fin N) (a b : Fin N) :
    signedSwapMat i j a b =
      if a = i ∧ b = j then -1
      else if a = j ∧ b = i then 1
      else if a = b ∧ a ≠ i ∧ a ≠ j then 1
      else 0 := rfl

lemma signedSwapMat_of_i (i j : Fin N) (hij : i ≠ j) (b : Fin N) (hbj : b ≠ j) :
    signedSwapMat i j i b = 0 := by
  unfold signedSwapMat
  split_ifs <;> try rfl
  · rcases ‹_ ∧ _› with ⟨_, rfl⟩; contradiction
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩; contradiction
  · rcases ‹_ ∧ _ ∧ _› with ⟨_, h1, _⟩; contradiction

lemma signedSwapMat_of_j (i j : Fin N) (hij : i ≠ j) (b : Fin N) (hbi : b ≠ i) :
    signedSwapMat i j j b = 0 := by
  unfold signedSwapMat
  split_ifs <;> try rfl
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩; contradiction
  · rcases ‹_ ∧ _› with ⟨_, rfl⟩; contradiction
  · rcases ‹_ ∧ _ ∧ _› with ⟨_, _, h2⟩; contradiction

lemma signedSwapMat_of_other (i j : Fin N) (hij : i ≠ j) (a : Fin N) (hai : a ≠ i) (haj : a ≠ j) (b : Fin N) (hba : b ≠ a) :
    signedSwapMat i j a b = 0 := by
  unfold signedSwapMat
  split_ifs <;> try rfl
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩; contradiction
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩; contradiction
  · rcases ‹_ ∧ _ ∧ _› with ⟨rfl, _, _⟩; contradiction

lemma signedSwapMat_column_i (i j : Fin N) (hij : i ≠ j) (c : Fin N) (hcj : c ≠ j) :
    signedSwapMat i j c i = 0 := by
  unfold signedSwapMat
  split_ifs <;> try rfl
  · rcases ‹_ ∧ _› with ⟨rfl, h⟩
    contradiction
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩
    contradiction
  · rcases ‹_ ∧ _ ∧ _› with ⟨rfl, _, _⟩
    contradiction

lemma signedSwapMat_column_j (i j : Fin N) (hij : i ≠ j) (c : Fin N) (hci : c ≠ i) :
    signedSwapMat i j c j = 0 := by
  unfold signedSwapMat
  split_ifs <;> try rfl
  · rcases ‹_ ∧ _› with ⟨rfl, _⟩
    contradiction
  · rcases ‹_ ∧ _› with ⟨rfl, h_ji⟩
    exact absurd h_ji hci
  · rcases ‹_ ∧ _ ∧ _› with ⟨rfl, _, h⟩
    contradiction

lemma signedSwapMat_mul_conjTranspose_entry (i j : Fin N) (hij : i ≠ j) (a b : Fin N) :
    (signedSwapMat i j * (signedSwapMat i j).conjTranspose) a b =
      if a = b then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hai : a = i
  · rw [hai]
    have h_sum : (∑ c, signedSwapMat i j i c * (signedSwapMat i j).conjTranspose c b)
        = signedSwapMat i j i j * (signedSwapMat i j).conjTranspose j b := by
      apply Finset.sum_eq_single j
      · intro c _ hcj
        rw [signedSwapMat_of_i i j hij c hcj, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    rw [h_sum]
    have h_ij : signedSwapMat i j i j = -1 := by
      unfold signedSwapMat; simp
    rw [h_ij, conjTranspose_apply]
    by_cases hbi : b = i
    · rw [hbi]
      have h_ii : signedSwapMat i j i j = -1 := by
        unfold signedSwapMat; simp
      rw [h_ii]
      simp [hij]
    · by_cases hbj : b = j
      · rw [hbj]
        have h_jj : signedSwapMat i j j j = 0 := by
          unfold signedSwapMat; simp [hij.symm]
        rw [h_jj]
        simp [hij]
      · have h_col : signedSwapMat i j b j = 0 := by
          apply signedSwapMat_column_j i j hij b hbi
        rw [h_col]
        simp [Ne.symm hbi]
  · by_cases haj : a = j
    · rw [haj]
      have h_sum : (∑ c, signedSwapMat i j j c * (signedSwapMat i j).conjTranspose c b)
          = signedSwapMat i j j i * (signedSwapMat i j).conjTranspose i b := by
        apply Finset.sum_eq_single i
        · intro c _ hci
          rw [signedSwapMat_of_j i j hij c hci, zero_mul]
        · intro hi; exact absurd (Finset.mem_univ _) hi
      rw [h_sum]
      have h_ji : signedSwapMat i j j i = 1 := by
        unfold signedSwapMat; simp [hij.symm]
      rw [h_ji, one_mul, conjTranspose_apply]
      by_cases hbj : b = j
      · rw [hbj]
        have h_jj : signedSwapMat i j j i = 1 := by
          unfold signedSwapMat; simp [hij.symm]
        rw [h_jj]
        simp [hij.symm]
      · by_cases hbi : b = i
        · rw [hbi]
          have h_ii : signedSwapMat i j i i = 0 := by
            unfold signedSwapMat; simp [hij]
          rw [h_ii]
          simp [hij.symm]
        · have h_col : signedSwapMat i j b i = 0 := by
            apply signedSwapMat_column_i i j hij b hbj
          rw [h_col]
          simp [Ne.symm hbj]
    · have h_sum : (∑ c, signedSwapMat i j a c * (signedSwapMat i j).conjTranspose c b)
          = signedSwapMat i j a a * (signedSwapMat i j).conjTranspose a b := by
        apply Finset.sum_eq_single a
        · intro c _ hca
          rw [signedSwapMat_of_other i j hij a hai haj c hca, zero_mul]
        · intro ha; exact absurd (Finset.mem_univ _) ha
      rw [h_sum]
      have h_aa : signedSwapMat i j a a = 1 := by
        unfold signedSwapMat; simp [hai, haj]
      rw [h_aa, one_mul, conjTranspose_apply]
      by_cases hab : b = a
      · rw [hab]
        have h_aa2 : signedSwapMat i j a a = 1 := by
          unfold signedSwapMat; simp [hai, haj]
        rw [h_aa2]
        simp [hai, haj]
      · by_cases hbi : b = i
        · rw [hbi]
          have h_col : signedSwapMat i j i a = 0 := by
            apply signedSwapMat_of_i i j hij a haj
          rw [h_col]
          simp [hai]
        · by_cases hbj : b = j
          · rw [hbj]
            have h_col : signedSwapMat i j j a = 0 := by
              apply signedSwapMat_of_j i j hij a hai
            rw [h_col]
            simp [haj]
          · have h_col : signedSwapMat i j b a = 0 := by
              apply signedSwapMat_of_other i j hij b hbi hbj a (Ne.symm hab)
            rw [h_col]
            simp [Ne.symm hab]

theorem signedSwapMat_mul_conjTranspose (i j : Fin N) (hij : i ≠ j) :
    signedSwapMat i j * (signedSwapMat i j).conjTranspose = 1 := by
  ext a b
  rw [signedSwapMat_mul_conjTranspose_entry i j hij a b]
  rw [one_apply]

lemma signedSwapMat_eq_swap_of_nonzero (i j : Fin N) (hij : i ≠ j) (σ : Equiv.Perm (Fin N))
    (h : ∀ a, signedSwapMat i j a (σ a) ≠ 0) :
    σ = Equiv.swap i j := by
  ext a
  by_cases hai : a = i
  · rw [hai]
    rw [Equiv.swap_apply_left]
    by_contra hc
    have hc' : σ i ≠ j := by
      intro h_eq
      rw [h_eq] at hc
      exact hc rfl
    have h0 := signedSwapMat_of_i i j hij (σ i) hc'
    exact h i h0
  · by_cases haj : a = j
    · rw [haj]
      rw [Equiv.swap_apply_right]
      by_contra hc
      have hc' : σ j ≠ i := by
        intro h_eq
        rw [h_eq] at hc
        exact hc rfl
      have h0 := signedSwapMat_of_j i j hij (σ j) hc'
      exact h j h0
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
      by_contra hc
      have hc' : σ a ≠ a := by
        intro h_eq
        rw [h_eq] at hc
        exact hc rfl
      have h0 := signedSwapMat_of_other i j hij a hai haj (σ a) hc'
      exact h a h0

lemma signedSwapMat_prod_eq_zero (i j : Fin N) (hij : i ≠ j) (σ : Equiv.Perm (Fin N))
    (hσ : σ ≠ Equiv.swap i j) :
    (∏ a, signedSwapMat i j a (σ a)) = 0 := by
  by_contra hc
  have h_nonzero : ∀ a, signedSwapMat i j a (σ a) ≠ 0 := by
    intro a
    by_contra h0
    have h_prod : (∏ x, signedSwapMat i j x (σ x)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ a) h0
    exact hc h_prod
  have heq := signedSwapMat_eq_swap_of_nonzero i j hij σ h_nonzero
  exact hσ heq

lemma prod_decomp_two {α : Type*} [DecidableEq α] [CommMonoid β] (s : Finset α) (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (f : α → β) :
    (∏ x ∈ s, f x) = f i * f j * ∏ x ∈ s \ insert i {j}, f x := by
  have h1 : s = insert i {j} ∪ (s \ insert i {j}) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxi : x = i
      · left; left; exact hxi
      · by_cases hxj : x = j
        · left; right; exact hxj
        · right; refine ⟨hx, ?_⟩; simp [hxi, hxj]
    · rintro ((rfl | rfl) | ⟨hx, _⟩) <;> assumption
  have h_disj : Disjoint (insert i {j} : Finset α) (s \ insert i {j}) := by
    rw [Finset.disjoint_iff_ne]
    rintro x hx y hy h_eq
    subst h_eq
    rw [Finset.mem_sdiff] at hy
    exact hy.2 hx
  nth_rw 1 [h1]
  rw [Finset.prod_union h_disj]
  have h2 : (∏ x ∈ (insert i {j} : Finset α), f x) = f i * f j := by
    rw [Finset.prod_insert, Finset.prod_singleton]
    simp [hij]
  rw [h2, mul_assoc]

lemma signedSwapMat_prod_swap (i j : Fin N) (hij : i ≠ j) :
    (∏ a, signedSwapMat i j a (Equiv.swap i j a)) = -1 := by
  have h_dec := prod_decomp_two (Finset.univ : Finset (Fin N)) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun a => signedSwapMat i j a (Equiv.swap i j a))
  rw [h_dec]
  have h_i : signedSwapMat i j i (Equiv.swap i j i) = -1 := by
    unfold signedSwapMat; simp
  have h_j : signedSwapMat i j j (Equiv.swap i j j) = 1 := by
    unfold signedSwapMat; simp [hij.symm]
  rw [h_i, h_j, mul_one]
  have h_rest : (∏ x ∈ Finset.univ \ (insert i {j} : Finset (Fin N)), signedSwapMat i j x (Equiv.swap i j x)) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hx
    rcases hx with ⟨hxi, hxj⟩
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
    unfold signedSwapMat; simp [hxi, hxj]
  rw [h_rest, mul_one]

lemma signedSwapMat_det (i j : Fin N) (hij : i ≠ j) :
    (signedSwapMat i j).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  have h_sum : (∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) * ∏ a, (signedSwapMat i j).transpose (σ a) a)
      = (Equiv.Perm.sign (Equiv.swap i j) : ℂ) * ∏ a, (signedSwapMat i j).transpose (Equiv.swap i j a) a := by
    apply Finset.sum_eq_single (Equiv.swap i j)
    · intro σ _ hσ
      have h_prod : (∏ a, (signedSwapMat i j).transpose (σ a) a) = 0 := by
        have h_eq : (∏ a, (signedSwapMat i j).transpose (σ a) a) = ∏ a, signedSwapMat i j a (σ a) := by
          refine Finset.prod_congr rfl (fun a _ => ?_)
          rfl
        rw [h_eq]
        exact signedSwapMat_prod_eq_zero i j hij σ hσ
      rw [h_prod, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_sum]
  have h_sign : (Equiv.Perm.sign (Equiv.swap i j) : ℂ) = -1 := by
    simp [Equiv.Perm.sign_swap hij]
  have h_swap : (∏ a, (signedSwapMat i j).transpose (Equiv.swap i j a) a) = -1 := by
    have h_eq : (∏ a, (signedSwapMat i j).transpose (Equiv.swap i j a) a) = ∏ a, signedSwapMat i j a (Equiv.swap i j a) := by
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rfl
    rw [h_eq]
    exact signedSwapMat_prod_swap i j hij
  rw [h_sign, h_swap]
  ring

/-- The SU(N) element representing the signed swap of i and j. -/
def signedSwapSU (i j : Fin N) (hij : i ≠ j) : Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ⟨signedSwapMat i j, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, signedSwapMat_det i j hij⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact signedSwapMat_mul_conjTranspose i j hij⟩

@[simp] lemma signedSwapSU_val (i j : Fin N) (hij : i ≠ j) :
    (signedSwapSU i j hij).val = signedSwapMat i j := rfl

lemma signedSwapSU_apply_right (i j : Fin N) (hij : i ≠ j)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m : Fin N) :
    ((U * signedSwapSU i j hij).val) m i = U.val m j := by
  have hmul : ((U * signedSwapSU i j hij).val : Matrix (Fin N) (Fin N) ℂ)
      = U.val * (signedSwapSU i j hij).val := rfl
  rw [hmul, signedSwapSU_val]
  show (U.val * signedSwapMat i j) m i = U.val m j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · have h_ji : signedSwapMat i j j i = 1 := by
      unfold signedSwapMat; simp [hij.symm]
    rw [h_ji, mul_one]
  · intro c _ hcj
    rw [signedSwapMat_column_i i j hij c hcj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

instance instIsHaarMeasureSUN (N_c : ℕ) [NeZero N_c] : IsHaarMeasure (sunHaarProb N_c) := by
  unfold sunHaarProb
  infer_instance

instance instIsMulRightInvariantSUN (N_c : ℕ) [NeZero N_c] : IsMulRightInvariant (sunHaarProb N_c) := by
  constructor
  intro g
  have h_left : (map (· * g) (sunHaarProb N_c)).IsMulLeftInvariant := by
    constructor
    intro l
    have h_comp : ((fun x : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => l * x) ∘ (fun x => x * g)) = (fun x => x * g) ∘ (fun x => l * x) := by
      funext x
      simp [mul_assoc]
    rw [map_map (continuous_const_mul l).measurable (continuous_mul_const g).measurable]
    rw [h_comp]
    rw [← map_map (continuous_mul_const g).measurable (continuous_const_mul l).measurable]
    rw [map_mul_left_eq_self]
  have h_eq : map (· * g) (sunHaarProb N_c) = (map (· * g) (sunHaarProb N_c)).haarScalarFactor (sunHaarProb N_c) • sunHaarProb N_c := by
    apply isMulInvariant_eq_smul_of_compactSpace
  have h_univ := congr_arg (fun (μ : Measure (Matrix.specialUnitaryGroup (Fin N_c) ℂ)) => μ univ) h_eq
  dsimp at h_univ
  rw [map_apply (continuous_mul_const g).measurable MeasurableSet.univ, preimage_univ] at h_univ
  rw [measure_univ] at h_univ
  simp at h_univ
  rw [h_eq]
  ext s hs
  rw [Measure.smul_apply]
  rw [ENNReal.smul_def]
  rw [← h_univ]
  rw [ENNReal.coe_one, one_smul]

theorem sunHaarProb_entry_normSq_eq (i j : Fin N) (hij : i ≠ j) (m : Fin N) :
    (∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N)) =
      ∫ U, (Complex.normSq (U.val m j) : ℝ) ∂(sunHaarProb N) := by
  set f := fun U : Matrix.specialUnitaryGroup (Fin N) ℂ => (Complex.normSq (U.val m i) : ℝ)
  have hinv : (∫ U, f U ∂(sunHaarProb N)) = ∫ U, f (U * signedSwapSU i j hij) ∂(sunHaarProb N) := by
    exact (MeasureTheory.integral_mul_right_eq_self f (signedSwapSU i j hij)).symm
  have h_pt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      f (U * signedSwapSU i j hij) = (Complex.normSq (U.val m j) : ℝ) := by
    intro U
    unfold f
    rw [signedSwapSU_apply_right i j hij U m]
  rw [hinv, MeasureTheory.integral_congr_ae (ae_of_all _ h_pt)]

lemma val_entry_normSq_integrable (m c : Fin N) :
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ => (Complex.normSq (U.val m c) : ℝ)) (sunHaarProb N) :=
  (Complex.continuous_normSq.comp (continuous_val_entry m c)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma unitary_row_normSq_sum (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m : Fin N) :
    ∑ c, (Complex.normSq (U.val m c) : ℝ) = 1 := by
  have hU : U.val ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have h_mul : U.val * U.val.conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hU
  have h_entry := congr_arg (fun A : Matrix (Fin N) (Fin N) ℂ => A m m) h_mul
  dsimp at h_entry
  rw [Matrix.mul_apply] at h_entry
  rw [Matrix.one_apply_eq] at h_entry
  have h_eq : (∑ c, Complex.normSq (U.val m c) : ℂ) = 1 := by
    calc (∑ c, Complex.normSq (U.val m c) : ℂ)
        = ∑ c, U.val m c * star (U.val m c) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          exact (Complex.mul_conj (U.val m c)).symm
      _ = ∑ c, U.val m c * U.val.conjTranspose c m := rfl
      _ = 1 := h_entry
  exact_mod_cast h_eq

lemma unitary_row_integral_sum (m : Fin N) :
    (∫ U, ∑ c, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N)) = 1 := by
  have h_pt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      ∑ c, (Complex.normSq (U.val m c) : ℝ) = 1 :=
    fun U => unitary_row_normSq_sum U m
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ h_pt)]
  simp

theorem sunHaarProb_entry_normSq_eq_inv_Nc (i : Fin N) (m : Fin N) :
    (∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N)) = (1 : ℝ) / N := by
  have h_sum : (∫ U, ∑ c, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N)) =
      ∑ c, ∫ U, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N) := by
    apply MeasureTheory.integral_finset_sum
    intro c _
    exact val_entry_normSq_integrable m c
  rw [unitary_row_integral_sum m] at h_sum
  have h_equal : ∀ c, (∫ U, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N))
      = ∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N) := by
    intro c
    by_cases hci : c = i
    · rw [hci]
    · exact sunHaarProb_entry_normSq_eq c i hci m
  have h_sum2 : (∑ c, ∫ U, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N))
      = (N : ℝ) * ∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N) := by
    calc (∑ c, ∫ U, (Complex.normSq (U.val m c) : ℝ) ∂(sunHaarProb N))
        = ∑ _c : Fin N, ∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N) :=
          Finset.sum_congr rfl (fun c _ => h_equal c)
      _ = (N : ℝ) * ∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N) := by
        simp
  rw [h_sum2] at h_sum
  have h_eq : ∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N) = 1 / (N : ℝ) := by
    have hN_pos : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have h_div : (N : ℝ) * (∫ U, (Complex.normSq (U.val m i) : ℝ) ∂(sunHaarProb N)) / (N : ℝ) = 1 / (N : ℝ) := by
      rw [← h_sum]
    rwa [mul_div_cancel_left₀ _ hN_pos] at h_div
  exact h_eq

theorem sunHaarProb_trace_normSq_integral_eq_one
    (N_c : ℕ) [NeZero N_c] :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ‖U.val.trace‖ ^ 2 ∂(sunHaarProb N_c) = 1 := by
  have h_norm : ∀ U : Matrix.specialUnitaryGroup (Fin N_c) ℂ,
      ‖U.val.trace‖ ^ 2 = Complex.normSq U.val.trace := fun U => by
    exact (complex_normSq_eq_norm_sq U.val.trace).symm
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ h_norm)]
  have hR : (∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N_c))
        = ∑ i : Fin N_c, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c) := by
    have hpt_trace : ∀ U : Matrix.specialUnitaryGroup (Fin N_c) ℂ,
        U.val.trace * star U.val.trace = ((Complex.normSq U.val.trace : ℝ) : ℂ) :=
      fun U => Complex.mul_conj U.val.trace
    have hC :
        ((∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N_c) : ℝ) : ℂ)
          = ∑ i : Fin N_c, ((∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c) : ℝ) : ℂ) := by
      have step1 :
          ((∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N_c) : ℝ) : ℂ)
            = ∫ U, ((Complex.normSq U.val.trace : ℝ) : ℂ) ∂(sunHaarProb N_c) :=
        integral_ofReal.symm
      rw [step1]
      rw [show (fun U : Matrix.specialUnitaryGroup (Fin N_c) ℂ =>
              ((Complex.normSq U.val.trace : ℝ) : ℂ))
            = fun U => U.val.trace * star U.val.trace from by
          funext U; exact (hpt_trace U).symm]
      rw [integral_trace_mul_conj_trace_eq_sum]
      exact Finset.sum_congr rfl fun i _ => diag_integral_ofReal i
    have hRHS :
        (∑ i : Fin N_c, ((∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c) : ℝ) : ℂ))
          = (((∑ i : Fin N_c, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c)) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hRHS] at hC
    exact_mod_cast hC
  rw [hR]
  have h_eq : ∀ i : Fin N_c,
      (∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c)) = 1 / (N_c : ℝ) :=
    fun i => sunHaarProb_entry_normSq_eq_inv_Nc i i
  have h_sum : (∑ i : Fin N_c, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c))
      = (N_c : ℝ) * (1 / (N_c : ℝ)) := by
    calc (∑ i : Fin N_c, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N_c))
        = ∑ _i : Fin N_c, (1 / (N_c : ℝ)) := Finset.sum_congr rfl (fun i _ => h_eq i)
      _ = (N_c : ℝ) * (1 / (N_c : ℝ)) := by simp
  rw [h_sum]
  have hN_pos : (N_c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N_c
  exact mul_one_div_cancel hN_pos

end YangMills.ClayCore
