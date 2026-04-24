import Mathlib
import YangMills.P8_PhysicalGap.SpatialLocalityFramework
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# SUN_LiebRobin — v0.8.36

Concrete Lieb-Robinson bound for the SU(N) Yang-Mills lattice model.

## Import discipline
This module is explicit-input and does not need the concrete SU(N) Dirichlet
core; avoiding that import keeps the locality theorem independent of the
experimental Lie-derivative sidecar.

## Axiom count: 0
## Sorry count: 0
-/

namespace YangMills
open MeasureTheory Real

/-! ## Step 1: SU(N) Markov semigroup — explicit input -/

/-! ## Step 2: Lieb-Robinson bound — explicit physical inputs -/

/-! ## Step 3: Main theorem — proved from explicit inputs -/

/-- Exponential covariance decay for SU(N) local observables. -/
theorem sun_locality_to_covariance
    (N_c d : ℕ) [NeZero N_c]
    (sg : SymmetricMarkovTransport (sunHaarProb N_c))
    (hVar : HasVarianceDecay sg)
    (hLR : LiebRobinsonBound (d := d) sg)
    (A B : Finset (Site d))
    (F G : SUN_State_Concrete N_c → ℝ)
    (hF_loc : IsSpatialLocalObservable A F) (hG_loc : IsSpatialLocalObservable B G)
    (hF : Integrable F (sunHaarProb N_c))
    (hG : Integrable G (sunHaarProb N_c))
    (hF2 : Integrable (fun x => F x ^ 2) (sunHaarProb N_c))
    (hG2 : Integrable (fun x => G x ^ 2) (sunHaarProb N_c)) :
    ∃ γ : ℝ, 0 < γ ∧
    |∫ x, F x * G x ∂(sunHaarProb N_c) -
      (∫ x, F x ∂(sunHaarProb N_c)) * (∫ x, G x ∂(sunHaarProb N_c))| ≤
    2 * Real.exp (-(supportDist A B : ℝ)) *
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂(sunHaarProb N_c)) ^ 2 ∂(sunHaarProb N_c)) *
      Real.sqrt (∫ x, (G x - ∫ y, G y ∂(sunHaarProb N_c)) ^ 2 ∂(sunHaarProb N_c)) :=
  locality_to_static_covariance_v2
    A B sg hVar F G
    hF_loc hG_loc hF hG hF2 hG2
    hLR

#print axioms sun_locality_to_covariance

end YangMills
