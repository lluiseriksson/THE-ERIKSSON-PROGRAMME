import YangMills.RG.BalabanCMP116WilsonPlaquetteMixedLipschitz

/-!
# Physical local energy for the Wilson plaquette defect

This module removes the external generator radii from the local Hessian
estimate.  The L2 operator norm of an `su(N)` generator is bounded by its
trace-form norm, and the latter is exactly the repository's orthonormal Lie
coordinate norm.  The four edge coordinates are then combined in a local
Euclidean energy.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The matrix L2 operator norm of an `su(N)` element is bounded by its
trace-form Hilbert norm. -/
theorem norm_suLie_toMatrix_l2_opNorm_le (X : SuLie Nc) :
    ‖X.toMatrix‖ ≤ ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro x
  let A := X.toMatrix
  let y : EuclideanSpace ℂ (Fin Nc) :=
    (EuclideanSpace.equiv (Fin Nc) ℂ).symm (A *ᵥ x)
  have hcoord (i : Fin Nc) :
      ‖y i‖ ≤ ‖WithLp.toLp 2 (fun j => star (A i j))‖ * ‖x‖ := by
    have heq :
        y i = inner ℂ (WithLp.toLp 2 (fun j => star (A i j))) x := by
      simp [y, A, PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [heq]
    exact norm_inner_le_norm _ _
  have hsq : ‖y‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i : Fin Nc, ‖y i‖ ^ 2) ≤
          ∑ i : Fin Nc,
            (‖WithLp.toLp 2 (fun j => star (A i j))‖ * ‖x‖) ^ 2 := by
              gcongr with i
              exact hcoord i
      _ = (∑ i : Fin Nc,
          ‖WithLp.toLp 2 (fun j => star (A i j))‖ ^ 2) * ‖x‖ ^ 2 := by
            simp_rw [mul_pow]
            rw [Finset.sum_mul]
      _ = (∑ i : Fin Nc, ∑ j : Fin Nc, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            rw [PiLp.norm_sq_eq_of_L2]
            simp
      _ = matrixTraceInner A A * ‖x‖ ^ 2 := by
            congr 1
            symm
            simp [matrixTraceInner, Matrix.trace, Matrix.diag,
              Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply]
            rw [Finset.sum_comm]
      _ = ‖X‖ ^ 2 * ‖x‖ ^ 2 := by
            rw [← suLie_inner_def X X, real_inner_self_eq_norm_sq]
  have hsquare : ‖y‖ ^ 2 ≤ (‖X‖ * ‖x‖) ^ 2 := by
    simpa [mul_pow] using hsq
  change ‖y‖ ≤ ‖X‖ * ‖x‖
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsquare

/-- Oriented generator transport is contractive from physical Lie
coordinates to the matrix L2 operator norm. -/
theorem norm_orientedWilsonGenerator_le_coordinate
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    ‖orientedWilsonGenerator A e‖ ≤ ‖A (physicalBondOfEdge e)‖ := by
  let X : SuLie Nc := (suLieCoordIso Nc).symm
    (A (physicalBondOfEdge e))
  have hX : ‖X.toMatrix‖ ≤ ‖X‖ :=
    norm_suLie_toMatrix_l2_opNorm_le X
  have hnorm : ‖X‖ = ‖A (physicalBondOfEdge e)‖ := by
    exact (suLieCoordIso Nc).symm.norm_map _
  unfold orientedWilsonGenerator flatOrientedSuMatrixTangent
  split
  · simpa [X, hnorm] using hX
  · simpa [X, hnorm] using hX

/-- Squared physical coordinate energy on the four oriented slots of a
plaquette. -/
def physicalPlaquetteCochainEnergySq
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  ∑ k : Fin 4, ‖A (physicalBondOfEdge (p.edges k))‖ ^ 2

/-- Physical local Euclidean energy on one plaquette. -/
def physicalPlaquetteCochainEnergy
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  Real.sqrt (physicalPlaquetteCochainEnergySq A p)

theorem physicalPlaquetteCochainEnergy_nonneg
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    0 ≤ physicalPlaquetteCochainEnergy A p :=
  Real.sqrt_nonneg _

/-- Every slot coordinate is bounded by the local plaquette energy. -/
theorem norm_coordinate_le_physicalPlaquetteCochainEnergy
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    ‖A (physicalBondOfEdge (p.edges k))‖ ≤
      physicalPlaquetteCochainEnergy A p := by
  apply (Real.le_sqrt (norm_nonneg _)
    (by
      unfold physicalPlaquetteCochainEnergySq
      positivity)).2
  unfold physicalPlaquetteCochainEnergySq
  exact Finset.single_le_sum
    (fun i _ => sq_nonneg ‖A (physicalBondOfEdge (p.edges i))‖)
    (Finset.mem_univ k)

/-- Every oriented generator on the plaquette is bounded by the local
physical energy. -/
theorem norm_orientedWilsonGenerator_le_physicalPlaquetteCochainEnergy
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (k : Fin 4) :
    ‖orientedWilsonGenerator A (p.edges k)‖ ≤
      physicalPlaquetteCochainEnergy A p :=
  (norm_orientedWilsonGenerator_le_coordinate A (p.edges k)).trans
    (norm_coordinate_le_physicalPlaquetteCochainEnergy A p k)

/-- Local physical Wilson defect bound with no external generator scales. -/
theorem abs_ambientWilsonPlaquetteHessian_sub_trivial_le_energy
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    |ambientWilsonPlaquetteHessian U p
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A))
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B)) -
        ambientWilsonPlaquetteHessian
          (trivialPhysicalGaugeBackground d N Nc) p
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A))
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B))| ≤
      (Nc : ℝ) * (64 * ε *
        physicalPlaquetteCochainEnergy A p *
        physicalPlaquetteCochainEnergy B p) := by
  exact abs_ambientWilsonPlaquetteHessian_sub_trivial_le
    U ε hε hsmall A B p
    (physicalPlaquetteCochainEnergy A p)
    (physicalPlaquetteCochainEnergy B p)
    (physicalPlaquetteCochainEnergy_nonneg A p)
    (physicalPlaquetteCochainEnergy_nonneg B p)
    (norm_orientedWilsonGenerator_le_physicalPlaquetteCochainEnergy A p)
    (norm_orientedWilsonGenerator_le_physicalPlaquetteCochainEnergy B p)

end

end YangMills.RG
