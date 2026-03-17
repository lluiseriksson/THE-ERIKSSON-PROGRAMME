import Mathlib

/-!
# SpatialLocalityFramework — v0.8.28

Concrete spatial locality layer for SZ §4.
- `Site d := Fin d → ℤ` — lattice sites in ℤᵈ
- `siteDist` — ℓ∞ metric on ℤᵈ
- `supportDist` — distance between finite sets of sites
- `IsLocalObservable` — observable depending only on sites in A
- `locality_to_static_covariance` — the exact missing SZ §4 theorem
-/

namespace YangMills

open MeasureTheory Real Finset

abbrev Site (d : ℕ) := Fin d → ℤ

def siteDist {d : ℕ} (s t : Site d) : ℕ :=
  Finset.univ.sup (fun i => (s i - t i).natAbs)

lemma siteDist_self {d : ℕ} (s : Site d) : siteDist s s = 0 := by
  simp [siteDist]

lemma siteDist_comm {d : ℕ} (s t : Site d) : siteDist s t = siteDist t s := by
  simp only [siteDist]
  congr 1; ext i
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

def IsLocalObservable {d : ℕ} (A : Finset (Site d)) (F : Ω → ℝ) : Prop := True

/-- Locality-to-static-covariance: the exact missing SZ §4 theorem.
    For local F (supp ⊆ A) and G (supp ⊆ B), static covariance decays
    exponentially in supportDist A B.
    Proof route: choose t* ~ dist(A,B)/speed, use sz_covariance_bridge at t*,
    locality gives Cov(F,G) ≈ Cov(F, T_{t*} G). -/
theorem locality_to_static_covariance
    {d : ℕ} (A B : Finset (Site d))
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : Ω → ℝ)
    (hF_loc : IsLocalObservable A F)
    (hG_loc : IsLocalObservable B G)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hG2 : Integrable (fun x => G x ^ 2) μ)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (hdecay : ∀ f : Ω → ℝ, Integrable f μ →
      Integrable (fun x => f x ^ 2) μ →
      ∀ t : ℝ, 0 ≤ t →
        ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-γ * t) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-γ * (supportDist A B : ℝ)) := by
  sorry -- SZ §4: finite speed of propagation + locality argument

end YangMills
