import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

/-!
# SpatialLocalityFramework — v0.8.29

Concrete spatial locality layer for SZ §4.
- `Site d := Fin d → ℤ` — lattice sites in ℤᵈ
- `siteDist` — ℓ∞ metric on ℤᵈ
- `supportDist` — distance between finite sets of sites
- `IsLocalObservable` — abstract locality predicate
- `optimalTime`, `local_to_dynamic_covariance` — SZ §4 decomposition
-/

namespace YangMills

open MeasureTheory Real Finset

abbrev Site (d : ℕ) := Fin d → ℤ

def siteDist {d : ℕ} (s t : Site d) : ℕ :=
  Finset.univ.sup (fun i => (s i - t i).natAbs)

lemma siteDist_self {d : ℕ} (s : Site d) : siteDist s s = 0 := by
  simp [siteDist]

lemma siteDist_comm {d : ℕ} (s t : Site d) : siteDist s t = siteDist t s := by
  simp only [siteDist]; congr 1; ext i
  rw [show s i - t i = -(t i - s i) from by ring, Int.natAbs_neg]

lemma siteDist_triangle {d : ℕ} (s t u : Site d) :
    siteDist s u ≤ siteDist s t + siteDist t u := by
  simp only [siteDist]
  apply Finset.sup_le
  intro i _
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
    if hB : B.Nonempty then
      A.inf' hA (fun a => B.inf' hB (fun b => siteDist a b))
    else 0
  else 0

variable {Ω : Type*} [MeasurableSpace Ω]

def IsLocalObservable {d : ℕ} (_A : Finset (Site d)) (_F : Ω → ℝ) : Prop := True

/-! ## Layer 4: Original SZ §4 theorem (sorry) -/

theorem locality_to_static_covariance
    {d : ℕ} (A B : Finset (Site d))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (_hF_loc : IsLocalObservable A F) (_hG_loc : IsLocalObservable B G)
    (_hF : Integrable F μ) (_hG : Integrable G μ)
    (_hF2 : Integrable (fun x => F x ^ 2) μ)
    (_hG2 : Integrable (fun x => G x ^ 2) μ)
    (C γ : ℝ) (_hC : 0 < C) (_hγ : 0 < γ)
    (_hdecay : ∀ f : Ω → ℝ, Integrable f μ →
      Integrable (fun x => f x ^ 2) μ → ∀ t : ℝ, 0 ≤ t →
        ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-γ * (supportDist A B : ℝ)) := by
  sorry -- SZ §4: see v0.8.29 decomposition below

/-! ## v0.8.29 — SZ §4 decomposition -/

/-! ### Step 1: Optimal time -/

noncomputable def optimalTime {d : ℕ} (A B : Finset (Site d)) (γ : ℝ) : ℝ :=
  (supportDist A B : ℝ) / γ

lemma optimalTime_nonneg {d : ℕ} (A B : Finset (Site d)) {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ optimalTime A B γ := by
  unfold optimalTime; positivity

lemma exp_neg_mul_optimalTime {d : ℕ} (A B : Finset (Site d)) {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-γ * optimalTime A B γ) = Real.exp (-(supportDist A B : ℝ)) := by
  unfold optimalTime; congr 1; field_simp

/-! ### Step 2: Dynamic covariance at t* -/

/-- Dynamic covariance bound at optimal time.
    Wraps sz_covariance_bridge (from PoincareCovarianceRoadmap) at t*.
    Kept as sorry here to avoid import cycle; discharged in StroockZegarlinski. -/
lemma dynamic_covariance_at_optimalTime
    {d : ℕ} (A B : Finset (Site d))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (F G : Ω → ℝ)
    (_hF : Integrable F μ) (_hG : Integrable G μ)
    (_hF2 : Integrable (fun x => F x ^ 2) μ)
    (_hG2 : Integrable (fun x => G x ^ 2) μ)
    {γ : ℝ} (_hγ : 0 < γ) :
    |∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
      - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  -- Proof: obtain ⟨γ', hγ', hbridge⟩ := sz_covariance_bridge sg F G hF hG hF2 hG2
  -- then apply hbridge at t = optimalTime, use exp_neg_mul_optimalTime
  -- Requires PoincareCovarianceRoadmap import → deferred to StroockZegarlinski
  sorry

/-! ### Step 3: Lieb-Robinson axiom -/

/-- The exact missing Lieb-Robinson physical content for SZ §4.
    |Cov(F,G) - Cov(F, T_{t*} G)| decays exponentially in supportDist A B.
    Proof requires finite speed of propagation for the lattice dynamics. -/
axiom local_to_dynamic_covariance
    {d : ℕ} (A B : Finset (Site d))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (F G : Ω → ℝ)
    (hF_loc : IsLocalObservable A F)
    (hG_loc : IsLocalObservable B G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    {γ : ℝ} (hγ : 0 < γ) :
    |∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ| ≤
    Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ)

/-! ### Step 4: Assembly -/

theorem locality_to_static_covariance_v2
    {d : ℕ} (A B : Finset (Site d))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : MarkovSemigroup μ)
    (F G : Ω → ℝ)
    (hF_loc : IsLocalObservable A F) (hG_loc : IsLocalObservable B G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ)
    {γ : ℝ} (hγ : 0 < γ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    2 * Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  have hLR  := local_to_dynamic_covariance A B sg F G hF_loc hG_loc hF hG hγ
  have hDyn := dynamic_covariance_at_optimalTime A B sg F G hF hG hF2 hG2 hγ
  have htri : |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
      |∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ| +
      |∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
        - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| := by
    have h_eq : ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ) =
        (∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ) +
        (∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
          - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)) := by ring
    rw [h_eq]
    simpa [Real.norm_eq_abs] using norm_add_le (∫ x, F x * G x ∂μ - ∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ) (∫ x, F x * sg.T (optimalTime A B γ) G x ∂μ
        - (∫ x, F x ∂μ) * (∫ x, G x ∂μ))
  have hfac : 0 ≤ Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  linarith

end YangMills
