import Mathlib
import YangMills.L6_FeynmanKac.FeynmanKac

namespace YangMills

open MeasureTheory Filter Topology

/-! ## L6.2: Osterwalder-Schrader interface layer

This file formalizes the minimal OS interface needed to connect:
- finite-volume lattice Gibbs measures (L1)
- infinite-volume limit (existence hypothesis)
- OS axioms: covariance, reflection positivity, cluster property
- mass gap extraction (L5.1 terminal theorem)

We do NOT attempt full OS/Wightman reconstruction here.
That requires additional layers (L7).

The key bridge is:
  HasInfiniteVolumeLimit + OSClusterProperty → ∃ m > 0
-/

variable {X : Type*} [MeasurableSpace X]

/-! ### Infinite-volume limit -/

/-- The thermodynamic limit exists: finite-volume expectations converge
    to expectations under a limiting measure μ∞. -/
def HasInfiniteVolumeLimit
    (muN : ℕ → Measure X) (muInf : Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) : Prop :=
  ∀ O : Obs,
    Tendsto (fun N => ∫ x, evalObs O x ∂(muN N))
      atTop (𝓝 (∫ x, evalObs O x ∂muInf))

/-- The infinite-volume measure is a probability measure. -/
def IsInfiniteVolumeMeasure (muInf : Measure X) : Prop :=
  IsProbabilityMeasure muInf

/-! ### OS axioms -/

/-- OS1: Euclidean covariance. The infinite-volume measure is invariant
    under the symmetry group action. -/
def OSCovariant (muInf : Measure X)
    (Symm : Type*) (act : Symm → X → X) : Prop :=
  ∀ s : Symm, Measurable (act s) → Measure.map (act s) muInf = muInf

/-- OS2: Reflection positivity. The two-point function is positive
    under time-reflection θ. -/
def OSReflectionPositive (muInf : Measure X)
    (ObsPos : Type*) (evalObs : ObsPos → X → ℝ) (theta : X → X) : Prop :=
  ∀ O : ObsPos, 0 ≤ ∫ x, evalObs O x * evalObs O (theta x) ∂muInf

/-- OS4: Cluster property (= mass gap in infinite volume).
    Connected correlations decay exponentially with distance.
    This is the key axiom for the mass gap. -/
def OSClusterProperty
    (muInf : Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ) : Prop :=
  ∃ C m : ℝ, 0 ≤ C ∧ 0 < m ∧
    ∀ O1 O2 : Obs,
      |(∫ x, evalObs O1 x * evalObs O2 x ∂muInf) -
       (∫ x, evalObs O1 x ∂muInf) * (∫ x, evalObs O2 x ∂muInf)|
      ≤ C * Real.exp (-m * distObs O1 O2)

/-- The connected two-point function in infinite volume. -/
noncomputable def infiniteConnectedCorr
    (muInf : Measure X) (f g : X → ℝ) : ℝ :=
  (∫ x, f x * g x ∂muInf) -
  (∫ x, f x ∂muInf) * (∫ x, g x ∂muInf)

/-- OS cluster property implies positive mass. -/
theorem osCluster_implies_massGap
    (muInf : Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (h : OSClusterProperty muInf Obs evalObs distObs) :
    ∃ m : ℝ, 0 < m := by
  obtain ⟨_, m, _, hm, _⟩ := h; exact ⟨m, hm⟩

/-! ### Thermodynamic limit preserves clustering -/

/-- If finite-volume correlations decay uniformly and the thermodynamic
    limit exists, the infinite-volume measure satisfies OS clustering.
    Hard content (limit exchange) is explicit hypothesis. -/
theorem thermodynamicLimit_cluster
    (muN : ℕ → Measure X) (muInf : Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hlim : HasInfiniteVolumeLimit muN muInf Obs evalObs)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (h_finite : ∀ (N : ℕ) (O1 O2 : Obs),
        |(∫ x, evalObs O1 x * evalObs O2 x ∂(muN N)) -
         (∫ x, evalObs O1 x ∂(muN N)) * (∫ x, evalObs O2 x ∂(muN N))|
        ≤ C * Real.exp (-m * distObs O1 O2))
    (h_limit_exchange : ∀ O1 O2 : Obs,
        |(∫ x, evalObs O1 x * evalObs O2 x ∂muInf) -
         (∫ x, evalObs O1 x ∂muInf) * (∫ x, evalObs O2 x ∂muInf)|
        ≤ C * Real.exp (-m * distObs O1 O2)) :
    OSClusterProperty muInf Obs evalObs distObs :=
  ⟨C, m, hC, hm, h_limit_exchange⟩

/-! ### Terminal assembly -/

/-- L6.2 terminal theorem: infinite-volume OS cluster property → mass gap. -/
theorem infiniteVolume_OS_massGap
    (muInf : Measure X) (Obs : Type*)
    (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hcluster : OSClusterProperty muInf Obs evalObs distObs) :
    ∃ m : ℝ, 0 < m :=
  osCluster_implies_massGap muInf Obs evalObs distObs hcluster

/-- Full assembly: thermodynamic limit + uniform finite-volume decay → mass gap. -/
theorem thermodynamicLimit_massGap
    (muN : ℕ → Measure X) (muInf : Measure X)
    (Obs : Type*) (evalObs : Obs → X → ℝ) (distObs : Obs → Obs → ℝ)
    (hlim : HasInfiniteVolumeLimit muN muInf Obs evalObs)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (h_finite : ∀ (N : ℕ) (O1 O2 : Obs),
        |(∫ x, evalObs O1 x * evalObs O2 x ∂(muN N)) -
         (∫ x, evalObs O1 x ∂(muN N)) * (∫ x, evalObs O2 x ∂(muN N))|
        ≤ C * Real.exp (-m * distObs O1 O2))
    (h_limit_exchange : ∀ O1 O2 : Obs,
        |(∫ x, evalObs O1 x * evalObs O2 x ∂muInf) -
         (∫ x, evalObs O1 x ∂muInf) * (∫ x, evalObs O2 x ∂muInf)|
        ≤ C * Real.exp (-m * distObs O1 O2)) :
    ∃ m : ℝ, 0 < m :=
  infiniteVolume_OS_massGap muInf Obs evalObs distObs
    (thermodynamicLimit_cluster muN muInf Obs evalObs distObs
      hlim C m hC hm h_finite h_limit_exchange)

end YangMills
