import Mathlib
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# P8.3: Bałaban RG → DLR-LSI(α*) — repaired abstract interface

This file is intentionally **abstract**.

Reason:
the previous version mixed an abstract SU(N) interface
(`SUN_State`, `sunGibbsFamily`, `sunDirichletForm`) with concrete
identifiers from the newer `SUN_StateConstruction` / `SUN_DirichletCore`
stack (`sunHaarProb`, `sunDirichletForm_concrete`, etc.), creating a type
mismatch in the consumer `PhysicalMassGap.lean`.

The honest repair is:
* keep the SU(N) state space / Gibbs family / Dirichlet form abstract,
* isolate the geometric Haar-LSI input,
* isolate the Balaban RG uniform-LSI input,
* isolate the LSI → clustering bridge,
* derive `sun_gibbs_dlr_lsi` as a theorem from those explicit ingredients.

This restores a coherent P8 consumer layer without pretending that the
concrete `ClayCoreLSI → DLR_LSI` transfer has already been formalized here.
-/

namespace YangMills

open MeasureTheory Real

/-! ## Abstract SU(N) objects used by the P8 consumer layer -/

/-- Abstract state space for SU(N) gauge variables in the P8 consumer layer. -/
abbrev SUN_State (N_c : ℕ) : Type := SUN_State_Concrete N_c



/-- Abstract Dirichlet form on the SU(N) state space. -/
opaque sunDirichletForm (N_c : ℕ) : (SUN_State N_c → ℝ) → ℝ

/-- Abstract finite-volume Gibbs family for SU(N) Yang-Mills. -/
noncomputable opaque sunGibbsFamily (d N_c : ℕ) (β : ℝ) : ℕ → Measure (SUN_State N_c)

/-- Haar is a probability measure in the abstract P8 interface. -/
noncomputable instance instIsProbabilityMeasure_sunHaarProb
    (N_c : ℕ) [NeZero N_c] : IsProbabilityMeasure (sunHaarProb N_c) :=
  instIsProbabilityMeasureSUN N_c


/-! ## M1: single-site Haar LSI -/

/-- Abstract Bakry-Émery curvature-dimension predicate. -/
opaque BakryEmeryCD
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (E : (Ω → ℝ) → ℝ)
    (K : ℝ) : Prop

/-- Bakry-Émery criterion for LSI (Mathlib-side geometric gap). -/
axiom bakry_emery_lsi
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (K : ℝ)
    (hK : 0 < K) :
    BakryEmeryCD μ E K →
    LogSobolevInequality μ E K

/-- SU(N) satisfies the relevant Bakry-Émery lower bound. -/
axiom sun_bakry_emery_cd
    (N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c) :
    BakryEmeryCD
      (sunHaarProb N_c)
      (sunDirichletForm N_c)
      ((N_c : ℝ) / 4)

/-- Haar LSI for SU(N), assembled from the abstract Bakry-Émery input. -/
theorem sun_haar_lsi
    (N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c) :
    ∃ α_haar : ℝ, 0 < α_haar ∧
      LogSobolevInequality
        (sunHaarProb N_c)
        (sunDirichletForm N_c)
        α_haar := by
  refine ⟨(N_c : ℝ) / 4, by positivity, ?_⟩
  apply bakry_emery_lsi
    (sunHaarProb N_c)
    (sunDirichletForm N_c)
    ((N_c : ℝ) / 4)
    (by positivity)
  exact sun_bakry_emery_cd N_c hN_c

/-! ## M2: Balaban RG uniform LSI -/

/-- Clay-core input: RG promotes the single-site Haar LSI to a uniform
finite-volume DLR-LSI constant. -/
axiom balaban_rg_uniform_lsi
    (d N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ)
    (hβ : β ≥ β₀)
    (hβ₀ : 0 < β₀)
    (α_haar : ℝ)
    (hα_haar : 0 < α_haar)
    (hHaar :
      LogSobolevInequality
        (sunHaarProb N_c)
        (sunDirichletForm N_c)
        α_haar) :
    ∃ α_star : ℝ, 0 < α_star ∧
      ∀ L : ℕ,
        LogSobolevInequality
          (sunGibbsFamily d N_c β L)
          (sunDirichletForm N_c)
          α_star

/-! ## LSI → clustering bridge used by PhysicalMassGap -/

/-- Abstract Stroock–Zegarlinski style bridge:
uniform DLR-LSI implies exponential clustering. -/
axiom sz_lsi_to_clustering
    {Ω : Type*} [MeasurableSpace Ω]
    (gibbsFamily : ℕ → Measure Ω)
    (E : (Ω → ℝ) → ℝ)
    (α_star : ℝ) :
    DLR_LSI gibbsFamily E α_star →
    ∃ C ξ : ℝ, 0 < ξ ∧ 0 < C ∧
      ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ

/-! ## Assembly -/

/-- DLR-LSI for SU(N) Yang-Mills, assembled from M1 + M2. -/
theorem sun_gibbs_dlr_lsi
    (d N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ)
    (hβ : β ≥ β₀)
    (hβ₀ : 0 < β₀) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI
        (sunGibbsFamily d N_c β)
        (sunDirichletForm N_c)
        α_star := by
  obtain ⟨α_haar, hα_haar, hHaar⟩ :=
    sun_haar_lsi N_c hN_c
  obtain ⟨α_star, hα_star, hvol⟩ :=
    balaban_rg_uniform_lsi
      d N_c hN_c β β₀ hβ hβ₀
      α_haar hα_haar hHaar
  exact ⟨α_star, hα_star, hα_star, hvol⟩

/-- Corollary: exponential clustering for the SU(N) Gibbs family. -/
theorem sun_gibbs_clustering
    (d N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ)
    (hβ : β ≥ β₀)
    (hβ₀ : 0 < β₀) :
    ∃ C ξ : ℝ, 0 < ξ ∧ 0 < C ∧
      ∀ L : ℕ,
        ExponentialClustering
          (sunGibbsFamily d N_c β L)
          C ξ := by
  obtain ⟨α_star, _, hLSI⟩ :=
    sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀
  exact sz_lsi_to_clustering
    (sunGibbsFamily d N_c β)
    (sunDirichletForm N_c)
    α_star
    hLSI

end YangMills
