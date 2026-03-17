import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.MarkovVarianceDecay
import YangMills.P8_PhysicalGap.CovarianceLemmas

namespace YangMills
open MeasureTheory Real Finset

abbrev Site (d : ℕ) := Fin d → ℤ

def siteDist {d : ℕ} (s t : Site d) : ℕ :=
  Finset.univ.sup (fun i => (s i - t i).natAbs)

lemma siteDist_self {d : ℕ} (s : Site d) : siteDist s s = 0 := by simp [siteDist]

lemma siteDist_comm {d : ℕ} (s t : Site d) : siteDist s t = siteDist t s := by
  simp only [siteDist]; congr 1; ext i
  rw [show s i - t i = -(t i - s i) from by ring, Int.natAbs_neg]

lemma siteDist_triangle {d : ℕ} (s t u : Site d) :
    siteDist s u ≤ siteDist s t + siteDist t u := by
  simp only [siteDist]; apply Finset.sup_le; intro i _
  calc (s i - u i).natAbs
      = ((s i - t i) + (t i - u i)).natAbs := by ring_nf
    _ ≤ (s i - t i).natAbs + (t i - u i).natAbs := Int.natAbs_add_le _ _
    _ ≤ Finset.univ.sup (fun j => (s j - t j).natAbs) +
        Finset.univ.sup (fun j => (t j - u j).natAbs) := by
        gcongr
        · exact Finset.le_sup (f := fun j => (s j - t j).natAbs) (Finset.mem_univ i)
        · exact Finset.le_sup (f := fun j => (t j - u j).natAbs) (Finset.mem_univ i)

noncomputable def supportDist {d : ℕ} (A B : Finset (Site d)) : ℕ :=
  if hA : A.Nonempty then
    if hB : B.Nonempty then A.inf' hA (fun a => B.inf' hB (fun b => siteDist a b))
    else 0
  else 0

variable {Ω : Type*} [MeasurableSpace Ω]
def IsLocalObservable {d : ℕ} (_A : Finset (Site d)) (_F : Ω → ℝ) : Prop := True

theorem locality_to_static_covariance
    {d : ℕ} (A B : Finset (Site d)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (_hF_loc : IsLocalObservable A F) (_hG_loc : IsLocalObservable B G)
    (_hF : Integrable F μ) (_hG : Integrable G μ)
    (_hF2 : Integrable (fun x => F x ^ 2) μ) (_hG2 : Integrable (fun x => G x ^ 2) μ)
    (C γ : ℝ) (_hC : 0 < C) (_hγ : 0 < γ)
    (_hdecay : ∀ f : Ω → ℝ, Integrable f μ → Integrable (fun x => f x ^ 2) μ →
      ∀ t : ℝ, 0 ≤ t → ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-γ * (supportDist A B : ℝ)) := by sorry

noncomputable def optimalTime {d : ℕ} (A B : Finset (Site d)) (γ : ℝ) : ℝ :=
  (supportDist A B : ℝ) / γ

lemma optimalTime_nonneg {d : ℕ} (A B : Finset (Site d)) {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ optimalTime A B γ := by unfold optimalTime; positivity

lemma exp_neg_mul_optimalTime {d : ℕ} (A B : Finset (Site d)) {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-γ * optimalTime A B γ) = Real.exp (-(supportDist A B : ℝ)) := by
  unfold optimalTime; congr 1; field_simp

lemma dynamic_covariance_at_optimalTime
    {d : ℕ} (A B : Finset (Site d)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (F G : Ω → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ) :
    ∃ γ : ℝ, 0 < γ ∧
    |∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  obtain ⟨γ, hγ, hdecay⟩ := markov_variance_decay sg
  refine ⟨γ, hγ, ?_⟩
  set t := optimalTime A B γ
  have ht : 0 ≤ t := optimalTime_nonneg A B hγ
  have hTG  : Integrable (sg.T t G) μ := sg.T_integrable t G hG
  have hTG2 : Integrable (fun x => sg.T t G x ^ 2) μ := sg.T_sq_integrable t G hG2
  have hFv : Integrable (fun x => (F x - ∫ y, F y ∂μ) ^ 2) μ := by
    have h_eq : (fun x => (F x - ∫ y, F y ∂μ) ^ 2) =ᵐ[μ]
        (fun x => F x ^ 2 - (2 * ∫ y, F y ∂μ) * F x + (∫ y, F y ∂μ) ^ 2) :=
      ae_of_all _ fun x => by ring
    exact (hF2.sub (hF.const_mul _)).add (integrable_const _) |>.congr h_eq.symm
  have hTGv : Integrable (fun x => (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2) μ := by
    have h_eq : (fun x => (sg.T t G x - ∫ y, sg.T t G y ∂μ) ^ 2) =ᵐ[μ]
        (fun x => sg.T t G x ^ 2 - (2 * ∫ y, sg.T t G y ∂μ) * sg.T t G x
          + (∫ y, sg.T t G y ∂μ) ^ 2) :=
      ae_of_all _ fun x => by ring
    exact (hTG2.sub (hTG.const_mul _)).add (integrable_const _) |>.congr h_eq.symm
  have hFGT : Integrable (fun x => F x * sg.T t G x) μ := by
    apply Integrable.mono (hF2.add hTG2)
    · exact hF.aestronglyMeasurable.mul hTG.aestronglyMeasurable
    · apply ae_of_all; intro x
      have h1 : 0 ≤ F x ^ 2 + sg.T t G x ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have h2 : |F x * sg.T t G x| ≤ F x ^ 2 + sg.T t G x ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|F x| - |sg.T t G x|), sq_abs (F x), sq_abs (sg.T t G x),
                   abs_nonneg (F x), abs_nonneg (sg.T t G x)]
      simpa [Real.norm_eq_abs, abs_of_nonneg h1] using h2
  have hstat : ∫ x, sg.T t G x ∂μ = ∫ x, G x ∂μ := sg.T_stat t G hG
  have hCS_raw := covariance_le_sqrt_var F (sg.T t G) hF hTG hFv hTGv hFGT
  have hCS : |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    simpa [hstat] using hCS_raw
  have hdec := hdecay G hG hG2 t ht
  have hsqrt_exp : Real.sqrt (Real.exp (-2 * γ * t)) = Real.exp (-γ * t) := by
    have hmul : Real.exp (-2 * γ * t) = Real.exp (-γ * t) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hmul, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hsqrt_decay :
      Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
    calc Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ)
        ≤ Real.sqrt (Real.exp (-2 * γ * t) * ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
            Real.sqrt_le_sqrt (by simpa [hstat] using hdec)
      _ = Real.sqrt (Real.exp (-2 * γ * t)) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
            Real.sqrt_mul (Real.exp_nonneg _) _
      _ = Real.exp (-γ * t) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by rw [hsqrt_exp]
  have hexp := exp_neg_mul_optimalTime A B hγ
  calc |∫ x, F x * sg.T t G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (sg.T t G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := hCS
    _ ≤ Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          (Real.exp (-γ * t) * Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hsqrt_decay (Real.sqrt_nonneg _)
    _ = Real.exp (-γ * t) *
          Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by ring
    _ = Real.exp (-(supportDist A B : ℝ)) *
          Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
          Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by rw [hexp]

axiom local_to_dynamic_covariance
    {d : ℕ} (A B : Finset (Site d)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (F G : Ω → ℝ)
    (hF_loc : IsLocalObservable A F) (hG_loc : IsLocalObservable B G)
    (hF : Integrable F μ) (hG : Integrable G μ) {γ : ℝ} (hγ : 0 < γ) :
    |∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ| ≤
    Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)

theorem locality_to_static_covariance_v2
    {d : ℕ} (A B : Finset (Site d)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ) (F G : Ω → ℝ)
    (hF_loc : IsLocalObservable A F) (hG_loc : IsLocalObservable B G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ) :
    ∃ γ : ℝ, 0 < γ ∧
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    2 * Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  obtain ⟨γ, hγ, hDyn⟩ := dynamic_covariance_at_optimalTime A B sg F G hF hG hF2 hG2
  refine ⟨γ, hγ, ?_⟩
  have hLR := local_to_dynamic_covariance A B sg F G hF_loc hG_loc hF hG hγ
  have htri : |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      |∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ| +
      |∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
        - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| := by
    have h_eq : ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) =
        (∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ) +
        (∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
          - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)) := by ring
    rw [h_eq]
    simpa [Real.norm_eq_abs] using norm_add_le
      (∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ)
      (∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ))
  have hfac : 0 ≤ Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  linarith

end YangMills
