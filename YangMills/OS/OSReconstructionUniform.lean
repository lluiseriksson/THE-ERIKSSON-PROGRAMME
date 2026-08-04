import YangMills.OS.SpatialReconstruction
import YangMills.OS.DobrushinCorollary
import YangMills.OS.DobrushinTilt
import YangMills.OS.DobrushinTransport
import YangMills.OS.TransferGap

/-!
# Finite OS reconstruction with a volume-uniform transfer gap

This file is the composition theorem joining the finite-volume
Osterwalder--Schrader reconstruction lane to the Dobrushin gap lane.

The public endpoint does not assume reflection positivity, Perron data, a
vacuum, or a spectral gap. Its only analytic inputs are the explicit Ising
parameter window. Reflection positivity and identification of the physical
quotient are recorded separately below, because their observable types depend
on the reflection depth while the uniform-gap endpoint is quantified over the
spatial extent.
-/

open scoped BigOperators RealInnerProductSpace
open Finset

namespace YangMills.OS

open Dobrushin

/-! ## The OS input is a theorem about the Gibbs measure -/

/-- Reflection positivity of the finite Gibbs measure, in Gram-matrix form,
specialised to the spatial Ising weight used by the uniform-gap theorem. -/
theorem os_ising_measure_gram_nonneg (beta gamma : ℝ) (hbeta : 0 ≤ beta)
    (L m : ℕ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin (L + 1) → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∑ X : Fin ((m + 1) + (m + 1)) → (Fin (L + 1) → Fin 2),
          (starRingEnd ℂ) (F i (pastOf X)) * F j (futRevOf X) *
            ((gibbsWeight (sliceW gamma L) beta (N := m + 1 + m) X : ℝ) : ℂ))
        = (r : ℂ) := by
  exact gibbsSum_reflected_gram_nonneg (sliceW gamma L) hbeta c F

/-- The null space divided out in OS reconstruction is exactly the kernel of
the boundary collapse map; it is not an independently postulated subspace. -/
theorem os_ising_null_space_iff (beta gamma : ℝ) (L m : ℕ)
    (F : (Fin (m + 1) → (Fin (L + 1) → Fin 2)) → ℂ) :
    F ∈ LinearMap.ker (collapseL (sliceW gamma L) beta m) ↔
      osPairingSite (sliceW gamma L) beta m F = 0 := by
  exact mem_ker_collapseL_iff (sliceW_pos gamma L) beta m F

/-- The reconstructed physical space, as an explicit linear equivalence from
the OS quotient to boundary vectors. -/
noncomputable def osIsingPhysicalEquiv (beta gamma : ℝ) (L m : ℕ) :
    (((Fin (m + 1) → (Fin (L + 1) → Fin 2)) → ℂ) ⧸
        LinearMap.ker (collapseL (sliceW gamma L) beta m))
      ≃ₗ[ℂ] ((Fin (L + 1) → Fin 2) → ℂ) :=
  physicalEquiv (sliceW_pos gamma L) beta m

/-- The defining matrix element of the forced transfer operator is literally
the reflected Gibbs two-point sum, one time step further apart. -/
theorem os_ising_transfer_is_measure_sum (beta gamma : ℝ) (L m : ℕ)
    (F G : (Fin (m + 1) → (Fin (L + 1) → Fin 2)) → ℂ) :
    siteForm (sliceW gamma L)
        (collapse (sliceW gamma L) beta m F)
        (transferOp (sliceW gamma L) beta
          (collapse (sliceW gamma L) beta m G))
      = ∑ X : Fin ((m + 1) + (m + 1)) → (Fin (L + 1) → Fin 2),
          (starRingEnd ℂ) (F (pastOf X)) * G (futRevOf X) *
            ((gibbsWeight (sliceW gamma L) beta (N := m + 1 + m) X : ℝ) : ℂ) := by
  exact osPairing_transfer_gibbsSum (sliceW_pos gamma L) beta m F G

/-! ## The volume-uniform endpoint -/

/-- **Finite OS reconstruction with a volume-uniform transfer gap.**

Inside the explicit Dobrushin window there is one `mass > 0`, independent of
the spatial extent `L`, such that the normalised symmetrised transfer operator
has a positive unit vacuum, fixes that vacuum, has projected norm at most
`exp (-mass)`, and consequently has connected correlations decaying at that
same rate. The last clause is the exact intertwining with the transfer
operator forced by the OS site/bond forms.

Crucially, neither the Perron data nor any gap or clustering assertion occurs
among the hypotheses. -/
theorem os_reconstruction_uniform_gap (beta gamma : ℝ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hwindow : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha) :
    ∃ mass : ℝ, 0 < mass ∧ ∀ L : ℕ,
      ∃ (lambda : ℝ) (Omega : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lambda ∧
        (∀ sigma, 0 < Omega sigma) ∧
        (∀ sigma, ∑ tau,
          tiltKernel (sliceW gamma L) beta lambda sigma tau * Omega tau =
            Omega sigma) ∧
        VacuumTransfer
          (opOf (tiltKernel (sliceW gamma L) beta lambda)) (vacOf Omega) ∧
        ‖projectedTransfer
            (opOf (tiltKernel (sliceW gamma L) beta lambda)) (vacOf Omega)‖
          ≤ Real.exp (-mass) ∧
        (∀ (v : EuclideanSpace ℝ (Fin (L + 1) → Fin 2)) (n : ℕ),
          |connCorr (opOf (tiltKernel (sliceW gamma L) beta lambda))
              (vacOf Omega) v n|
            ≤ ‖v‖ ^ 2 * (Real.exp (-mass)) ^ n) ∧
        (∀ u : (Fin (L + 1) → Fin 2) → ℂ,
          transferOp (sliceW gamma L) beta
              (sqrtWeightEquiv (sliceW gamma L) (sliceW_pos gamma L) u)
            = sqrtWeightEquiv (sliceW gamma L) (sliceW_pos gamma L)
                (symWeightedOp (sliceW gamma L) beta u)) := by
  obtain ⟨mass, hmass, hL⟩ :=
    dobrushin_ising_uniform_gap beta gamma halpha0 halpha1 hwindow
  refine ⟨mass, hmass, fun L => ?_⟩
  obtain ⟨lambda, Omega, hlambda, hOmega, hfix, hgap⟩ := hL L
  have htransfer : VacuumTransfer
      (opOf (tiltKernel (sliceW gamma L) beta lambda)) (vacOf Omega) :=
    vacuumTransfer_opOf _ _
      (tiltKernel_symm (sliceW gamma L) beta lambda) hOmega hfix
  refine ⟨lambda, Omega, hlambda, hOmega, hfix, htransfer, hgap, ?_, ?_⟩
  · intro v n
    exact clustering_of_gap htransfer hgap v n
  · intro u
    exact transferOp_sqrtWeightEquiv (sliceW_pos gamma L) beta u

end YangMills.OS
