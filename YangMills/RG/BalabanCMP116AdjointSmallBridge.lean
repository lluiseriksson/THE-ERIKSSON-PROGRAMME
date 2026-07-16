import YangMills.RG.BalabanCMP116InteractingPrecision
import YangMills.RG.BalabanCMP116WilsonPlaquetteEnergy

/-!
# Fundamental-link smallness implies adjoint smallness

The complete interacting precision initially uses a model-independent
adjoint-smallness hypothesis.  For the concrete matrix adjoint model this
hypothesis follows from the same L2 operator-norm smallness imposed on Wilson
links.  The proof uses an instance-safe Frobenius packaging and the mixed
operator/Frobenius inequalities.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Frobenius packaging of a matrix as one Euclidean vector, avoiding a
second competing matrix norm instance. -/
def matrixFrobEuclid
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    EuclideanSpace ℂ (Fin Nc × Fin Nc) :=
  WithLp.toLp 2 fun p => A p.1 p.2

@[simp]
theorem matrixFrobEuclid_apply
    (A : Matrix (Fin Nc) (Fin Nc) ℂ)
    (p : Fin Nc × Fin Nc) :
    matrixFrobEuclid A p = A p.1 p.2 := rfl

theorem matrixFrobEuclid_add
    (A B : Matrix (Fin Nc) (Fin Nc) ℂ) :
    matrixFrobEuclid (A + B) =
      matrixFrobEuclid A + matrixFrobEuclid B := by
  rfl

theorem matrixFrobEuclid_sub
    (A B : Matrix (Fin Nc) (Fin Nc) ℂ) :
    matrixFrobEuclid (A - B) =
      matrixFrobEuclid A - matrixFrobEuclid B := by
  rfl

/-- The squared packaged Frobenius norm is the trace quadratic form. -/
theorem norm_matrixFrobEuclid_sq
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖matrixFrobEuclid A‖ ^ 2 = matrixTraceInner A A := by
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ p : Fin Nc × Fin Nc, ‖A p.1 p.2‖ ^ 2) =
      matrixTraceInner A A
  rw [Fintype.sum_prod_type]
  symm
  simp [matrixTraceInner, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply]
  rw [Finset.sum_comm]

/-- The Hilbert norm on `SuLie` is literally the packaged Frobenius norm of
its matrix. -/
theorem norm_suLie_eq_norm_matrixFrobEuclid
    (X : SuLie Nc) :
    ‖X‖ = ‖matrixFrobEuclid X.toMatrix‖ := by
  have hsq :
      ‖X‖ ^ 2 = ‖matrixFrobEuclid X.toMatrix‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq X, suLie_inner_def,
      ← norm_matrixFrobEuclid_sq]
  nlinarith [norm_nonneg X, norm_nonneg (matrixFrobEuclid X.toMatrix)]

/-- One matrix column as a Euclidean vector. -/
def matrixColumnEuclid
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) (j : Fin Nc) :
    EuclideanSpace ℂ (Fin Nc) :=
  WithLp.toLp 2 fun i => A i j

@[simp]
theorem matrixColumnEuclid_apply
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) (j i : Fin Nc) :
    matrixColumnEuclid A j i = A i j := rfl

/-- Left multiplication is controlled by the L2 operator norm on the left
and the Frobenius norm on the right. -/
theorem norm_matrixFrobEuclid_mul_left_le
    (B C : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖matrixFrobEuclid (B * C)‖ ≤
      ‖B‖ * ‖matrixFrobEuclid C‖ := by
  have hcol (j : Fin Nc) :
      ‖matrixColumnEuclid (B * C) j‖ ≤
        ‖B‖ * ‖matrixColumnEuclid C j‖ := by
    let c : EuclideanSpace ℂ (Fin Nc) := matrixColumnEuclid C j
    have h := B.l2_opNorm_mulVec c
    simpa [c, matrixColumnEuclid, Matrix.mul_apply,
      Matrix.mulVec, dotProduct] using h
  have hsq :
      ‖matrixFrobEuclid (B * C)‖ ^ 2 ≤
        (‖B‖ * ‖matrixFrobEuclid C‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow,
      EuclideanSpace.norm_sq_eq]
    change
      (∑ p : Fin Nc × Fin Nc, ‖(B * C) p.1 p.2‖ ^ 2) ≤
        ‖B‖ ^ 2 *
          (∑ p : Fin Nc × Fin Nc, ‖C p.1 p.2‖ ^ 2)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm]
    have hsum :
        (∑ j : Fin Nc, ∑ i : Fin Nc, ‖(B * C) i j‖ ^ 2) ≤
          ∑ j : Fin Nc,
            (‖B‖ * ‖matrixColumnEuclid C j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hj := (sq_le_sq₀
        (norm_nonneg (matrixColumnEuclid (B * C) j))
        (mul_nonneg (norm_nonneg B)
          (norm_nonneg (matrixColumnEuclid C j)))).2 (hcol j)
      simpa [EuclideanSpace.norm_sq_eq, matrixColumnEuclid] using hj
    calc
      (∑ j : Fin Nc, ∑ i : Fin Nc, ‖(B * C) i j‖ ^ 2) ≤
          ∑ j : Fin Nc,
            (‖B‖ * ‖matrixColumnEuclid C j‖) ^ 2 := hsum
      _ = ‖B‖ ^ 2 *
          (∑ j : Fin Nc, ∑ i : Fin Nc, ‖C i j‖ ^ 2) := by
        simp_rw [mul_pow, EuclideanSpace.norm_sq_eq, matrixColumnEuclid]
        rw [Finset.mul_sum]
      _ = ‖B‖ ^ 2 *
          (∑ i : Fin Nc, ∑ j : Fin Nc, ‖C i j‖ ^ 2) := by
        rw [Finset.sum_comm]
  exact (sq_le_sq₀
    (norm_nonneg (matrixFrobEuclid (B * C)))
    (mul_nonneg (norm_nonneg B)
      (norm_nonneg (matrixFrobEuclid C)))).1 hsq

/-- Conjugate transpose preserves the packaged Frobenius norm. -/
theorem norm_matrixFrobEuclid_conjTranspose
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖matrixFrobEuclid Aᴴ‖ = ‖matrixFrobEuclid A‖ := by
  have hsq :
      ‖matrixFrobEuclid Aᴴ‖ ^ 2 =
        ‖matrixFrobEuclid A‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change
      (∑ p : Fin Nc × Fin Nc, ‖Aᴴ p.1 p.2‖ ^ 2) =
        ∑ p : Fin Nc × Fin Nc, ‖A p.1 p.2‖ ^ 2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Matrix.conjTranspose_apply, norm_star]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg (matrixFrobEuclid Aᴴ),
    norm_nonneg (matrixFrobEuclid A)]

/-- Right multiplication is controlled by the Frobenius norm on the left
and the L2 operator norm on the right. -/
theorem norm_matrixFrobEuclid_mul_right_le
    (C B : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖matrixFrobEuclid (C * B)‖ ≤
      ‖matrixFrobEuclid C‖ * ‖B‖ := by
  calc
    ‖matrixFrobEuclid (C * B)‖ =
        ‖matrixFrobEuclid (C * B)ᴴ‖ :=
      (norm_matrixFrobEuclid_conjTranspose (C * B)).symm
    _ = ‖matrixFrobEuclid (Bᴴ * Cᴴ)‖ := by
      rw [Matrix.conjTranspose_mul]
    _ ≤ ‖Bᴴ‖ * ‖matrixFrobEuclid Cᴴ‖ :=
      norm_matrixFrobEuclid_mul_left_le Bᴴ Cᴴ
    _ = ‖matrixFrobEuclid C‖ * ‖B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose,
        norm_matrixFrobEuclid_conjTranspose, mul_comm]

/-- Every concrete special-unitary matrix has L2 operator norm one. -/
theorem norm_SUN_coe_l2_opNorm
    (g : SUN Nc) :
    ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = 1 := by
  let M : Matrix (Fin Nc) (Fin Nc) ℂ := g
  have hunitary :
      M ∈ Matrix.unitaryGroup (Fin Nc) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1
  have hmul : Mᴴ * M = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hunitary)
  have hone :
      ‖(1 : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = 1 := by
    rw [show (1 : Matrix (Fin Nc) (Fin Nc) ℂ) =
        Matrix.diagonal (fun _ => 1) by ext i j; simp]
    rw [Matrix.l2_opNorm_diagonal]
    simp
  have hsq : ‖M‖ * ‖M‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hmul]
    exact hone
  nlinarith [norm_nonneg M]

/-- Conjugation by a special-unitary matrix is Lipschitz near the identity
from the L2 operator norm to the Frobenius norm, with the sharp elementary
factor two. -/
theorem norm_matrixFrobEuclid_su_conjugation_sub_self_le
    (g : SUN Nc) (A : Matrix (Fin Nc) (Fin Nc) ℂ)
    {ε : ℝ}
    (hsmall :
      ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε) :
    ‖matrixFrobEuclid
        ((g : Matrix (Fin Nc) (Fin Nc) ℂ) * A *
            (g : Matrix (Fin Nc) (Fin Nc) ℂ)ᴴ - A)‖ ≤
      2 * ε * ‖matrixFrobEuclid A‖ := by
  let G : Matrix (Fin Nc) (Fin Nc) ℂ := g
  have hG : ‖G‖ = 1 := norm_SUN_coe_l2_opNorm g
  have hGH : ‖Gᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose, hG]
  have hsmallH : ‖Gᴴ - 1‖ ≤ ε := by
    calc
      ‖Gᴴ - 1‖ = ‖(G - 1)ᴴ‖ := by simp
      _ = ‖G - 1‖ := Matrix.l2_opNorm_conjTranspose _
      _ ≤ ε := hsmall
  have hε : 0 ≤ ε := le_trans (norm_nonneg (G - 1)) hsmall
  have hAG :
      ‖matrixFrobEuclid (A * Gᴴ)‖ ≤
        ‖matrixFrobEuclid A‖ * ‖Gᴴ‖ :=
    norm_matrixFrobEuclid_mul_right_le A Gᴴ
  have hsplit :
      G * A * Gᴴ - A =
        (G - 1) * (A * Gᴴ) + A * (Gᴴ - 1) := by
    noncomm_ring
  rw [hsplit, matrixFrobEuclid_add]
  calc
    ‖matrixFrobEuclid ((G - 1) * (A * Gᴴ)) +
        matrixFrobEuclid (A * (Gᴴ - 1))‖ ≤
        ‖matrixFrobEuclid ((G - 1) * (A * Gᴴ))‖ +
          ‖matrixFrobEuclid (A * (Gᴴ - 1))‖ := norm_add_le _ _
    _ ≤ ‖G - 1‖ * ‖matrixFrobEuclid (A * Gᴴ)‖ +
          ‖matrixFrobEuclid A‖ * ‖Gᴴ - 1‖ :=
      add_le_add
        (norm_matrixFrobEuclid_mul_left_le (G - 1) (A * Gᴴ))
        (norm_matrixFrobEuclid_mul_right_le A (Gᴴ - 1))
    _ ≤ ε * (‖matrixFrobEuclid A‖ * ‖Gᴴ‖) +
          ‖matrixFrobEuclid A‖ * ε := by
      exact add_le_add
        (mul_le_mul hsmall hAG
          (norm_nonneg (matrixFrobEuclid (A * Gᴴ))) hε)
        (mul_le_mul_of_nonneg_left hsmallH
          (norm_nonneg (matrixFrobEuclid A)))
    _ = 2 * ε * ‖matrixFrobEuclid A‖ := by
      rw [hGH]
      ring

/-- The concrete adjoint action on `su(Nc)` inherits the factor-two
Lipschitz estimate from fundamental-link operator-norm smallness. -/
theorem norm_suAdActLin_sub_self_le
    (g : SUN Nc) (X : SuLie Nc) {ε : ℝ}
    (hsmall :
      ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ ε) :
    ‖suAdActLin g X - X‖ ≤ 2 * ε * ‖X‖ := by
  rw [norm_suLie_eq_norm_matrixFrobEuclid,
    norm_suLie_eq_norm_matrixFrobEuclid]
  change
    ‖matrixFrobEuclid
      (suAdAct g X.toMatrix - X.toMatrix)‖ ≤
        2 * ε * ‖matrixFrobEuclid X.toMatrix‖
  exact norm_matrixFrobEuclid_su_conjugation_sub_self_le
    g X.toMatrix hsmall

/-- For the concrete matrix adjoint model, the physical Wilson
operator-norm smallness hypothesis implies adjoint smallness with the explicit
factor-two loss.  This removes the independent adjoint-smallness assumption
from the complete interacting precision. -/
theorem physicalAdjointSmallBackground_of_wilson
    (U : PhysicalGaugeBackground d N Nc) {ε : ℝ}
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    PhysicalAdjointSmallBackground
      (matrixSUNAdjointModel Nc) U (2 * ε) := by
  intro b X
  let Y : SuLie Nc := (suLieCoordIso Nc).symm X
  have hsu :
      ‖suAdActLin (U (positiveEdgeOfPhysicalBond b)) Y - Y‖ ≤
        2 * ε * ‖Y‖ :=
    norm_suAdActLin_sub_self_le
      (U (positiveEdgeOfPhysicalBond b)) Y (hsmall b)
  have hcoord :
      ‖(suLieCoordIso Nc)
          (suAdActLin (U (positiveEdgeOfPhysicalBond b)) Y - Y)‖ ≤
        2 * ε * ‖(suLieCoordIso Nc) Y‖ := by
    simpa only [(suLieCoordIso Nc).norm_map] using hsu
  change
    ‖(suLieCoordIso Nc)
          (suAdActLin
            (U (positiveEdgeOfPhysicalBond b))
            ((suLieCoordIso Nc).symm X)) - X‖ ≤
      (2 * ε) * ‖X‖
  simpa [Y, map_sub] using hcoord

/-- Complete interacting-defect budget expressed solely in the fundamental
Wilson smallness parameter. -/
def cmp116ConcreteInteractingWilsonGaugeDefectBudget
    (d Nc : ℕ) (ε : ℝ) : ℝ :=
  cmp116InteractingWilsonGaugeDefectBudget d Nc ε (2 * ε)

/-- The complete Wilson-plus-gauge defect is controlled by the single
fundamental-link smallness hypothesis. -/
theorem norm_interactingWilsonGaugeDefectCLM_le_of_wilson
    (U : PhysicalGaugeBackground d N Nc)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    ‖interactingWilsonGaugeDefectCLM U‖ ≤
      cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε := by
  exact norm_interactingWilsonGaugeDefectCLM_le U hε
    (mul_nonneg (by positivity) hε) hsmall
    (physicalAdjointSmallBackground_of_wilson U hsmall)

/-- Coercivity of the flat precision survives for the concrete matrix model
under one physical Wilson-smallness condition. -/
theorem isCoerciveCLM_interactingWilsonGaugeBasePrecision_of_wilson
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : PhysicalGaugeBackground d N Nc)
    (Q : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (a c : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (hflat :
      IsCoerciveCLM
        (gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc)) Q a) c) :
    IsCoerciveCLM
      (interactingWilsonGaugeBasePrecisionCLM U Q a)
      (c - cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε) := by
  exact isCoerciveCLM_interactingWilsonGaugeBasePrecision
    U Q a c hε (mul_nonneg (by positivity) hε) hsmall
    (physicalAdjointSmallBackground_of_wilson U hsmall) hflat

end

end YangMills.RG
