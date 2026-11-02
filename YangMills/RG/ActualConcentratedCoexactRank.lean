import YangMills.RG.ActualConcentratedRepairMean
import YangMills.RG.CoexactFlatEnergy
import YangMills.RG.PhysicalAverageWeightRank

/-! Actual combined observation on the constructed coexact band.
No supplied injection, band dimension, repair annihilation or Hodge certificate. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem actualOriginDifference_codomain_finrank :
    finrank ℝ (Fin (d + 2) × Fin (d + 2) → SUNLieCoord Nc) =
      (d + 2)^2 * (Nc^2 - 1) := by
  rw [Module.finrank_pi_fintype]
  simp [SUNLieCoord, finrank_euclideanSpace, pow_two, Nat.mul_assoc]

noncomputable def actualConcentratedBandObservation (hNc : 2 ≤ Nc) (R : ℕ)
    (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F) (x0 : FinBox (d + 2) n) :
    coexactPositivePhysicalBand (d := d) (n := n) hNc R →ₗ[ℝ]
      F × (Fin (d + 2) × Fin (d + 2) → SUNLieCoord Nc) :=
  (L.toLinearMap.prod (actualOriginDifferenceLin x0)).comp
    (coexactPositivePhysicalBand (d := d) (n := n) hNc R).subtype

section Original
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (R : ℕ) (hR : 2 * R < n)
variable (x0 : FinBox (d + 2) n) (b : ℝ)
variable (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
variable (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
variable (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
variable (Phi : F → ℝ) (K delta radius c : ℝ)
variable (hdelta : 0 < delta) (hradius : 0 < radius)
variable (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
variable (hgap : 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2 < c)
variable (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
  gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
  ‖A‖ < radius → c * ‖A‖^2 ≤
    inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
    inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) + Phi (C A))

include hNc rho R hR x0 b C L hC hC0 Phi K delta radius c hdelta hradius hPhi hgap hlocal

theorem actualConcentrated_coexact_combined_injective :
    Function.Injective (actualConcentratedBandObservation hNc R L x0) := by
  classical
  intro u v huv
  let S := coexactPositivePhysicalBand (d := d) (n := n) hNc R
  let A : PhysicalGaugeOneCochain (d + 2) n Nc := u.val - v.val
  have hAS : A ∈ S := S.sub_mem u.property v.property
  have hLA : L A = 0 := by
    have h := congrArg Prod.fst huv
    change L u.val = L v.val at h
    change L (u.val - v.val) = 0
    rw [map_sub, h, sub_self]
  have hBA : actualOriginDifferenceLin x0 A = 0 := by
    have h := congrArg Prod.snd huv
    change actualOriginDifferenceLin x0 u.val = actualOriginDifferenceLin x0 v.val at h
    change actualOriginDifferenceLin x0 (u.val - v.val) = 0
    rw [map_sub, h, sub_self]
  let G := (gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc)).ker
  let T := (flatGaugeHodgeK0CLM (d + 2) n Nc rho +
    componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b)).toLinearMap
  have hAG : A ∈ G := coexactPositivePhysicalBand_div_zero hNc rho R A hAS
  have hb := local_derivative_kernel_quadratic_lower G T C L hC hC0 Phi K delta radius c
    hdelta hradius hPhi (by
      intro B hB hnorm
      have hdiv : gaugeConstraintQCLM rho
          (trivialPhysicalGaugeBackground (d + 2) n Nc) B = 0 := hB
      simpa [T, ContinuousLinearMap.add_apply, inner_add_right] using hlocal B hdiv hnorm)
    A hAG hLA
  change c * ‖A‖^2 ≤ inner ℝ A
    (flatGaugeHodgeK0CLM (d + 2) n Nc rho A +
      componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) at hb
  rw [inner_add_right, actualConcentrated_repair_energy_zero x0 b A hBA, add_zero] at hb
  let beta := 4 * Real.pi^2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ)^2 / (n : ℝ)^2
  have hupper : inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) ≤ beta * ‖A‖^2 :=
    coexactPositivePhysicalBand_hodge_le hNc rho R hR A hAS
  have hAz : A = 0 := by
    by_contra hne
    have hn : 0 < ‖A‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hg : 0 < (c - beta) * ‖A‖^2 := mul_pos (sub_pos.mpr hgap) hn
    nlinarith only [hb, hupper, hg]
  apply Subtype.ext
  exact sub_eq_zero.mp hAz

theorem actualConcentrated_coexact_rank :
    2 * R * (2 * R + 1)^(d + 1) ≤ finrank ℝ F + (d + 2)^2 * (Nc^2 - 1) := by
  have hi := actualConcentrated_coexact_combined_injective hNc rho R hR x0 b C L hC hC0
    Phi K delta radius c hdelta hradius hPhi hgap hlocal
  have h := LinearMap.finrank_le_finrank_of_injective hi
  rw [coexactPositivePhysicalBand_finrank hNc R hR, Module.finrank_prod,
    actualOriginDifference_codomain_finrank] at h
  exact h
end Original
end YangMills.RG
