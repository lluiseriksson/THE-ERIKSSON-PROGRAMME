import YangMills.RG.BalabanCMP89NeumannRectangularBranchResidueSum
import YangMills.RG.BalabanCMP89NeumannReflectionRepresentation
import YangMills.RG.BalabanCMP89CenteredGreenFourierSummability
import YangMills.RG.BalabanCMP85SourceMassParameterUniformComplexWindow

/-!
# CMP89 (2.42): full-lattice Green insertion into the Neumann image series

PRE-VALIDATION: draft source is present, its `.olean` has not yet been
materialized, and no result in this module is compiler-verified.

This module inserts one explicit full-lattice Green into the already sealed
rectangular reflection-image sum.  A single pair `(B0, delta0)` controls every
integer image and every reflection branch.  Absolute summability is proved
before any `tsum`/finite-sum exchange.

The final physical specialization uses the literal normalized CMP89 (2.48)
Fourier Green.  It does not assert the regional representation (2.42).
-/

namespace YangMills.RG

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- One explicit full-lattice kernel with one common amplitude and one common
signed-lattice decay rate.  The kernel and both constants are parameters of
the certificate type, rather than hidden choices. -/
structure CMP89FullLatticeGreenDecayCertificate
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E)
    (B0 delta0 : ℝ) : Prop where
  B0_nonneg : 0 ≤ B0
  delta0_pos : 0 < delta0
  bound : ∀ x y,
    ‖fullGreen x y‖ ≤
      B0 * cmp89SignedLatticeL1ExponentialWeight delta0 (x - y)

/-- One reflection branch of a kernel controlled by a common decay
certificate is absolutely summable. -/
theorem summable_cmp89NeumannRectangularBranchFullGreen
    {fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E}
    {B0 delta0 : ℝ}
    (C : CMP89FullLatticeGreenDecayCertificate fullGreen B0 delta0)
    {m x n : Fin d → ℤ} (hm : ∀ mu, 0 < m mu)
    (branch : CMP89NeumannReflectionBranch d) :
    Summable (fun k : Fin d → ℤ ↦
      fullGreen x (cmp89NeumannReflectionImage m n k branch)) := by
  apply Summable.of_norm_bounded
    ((summable_cmp89NeumannRectangularBranchImageWeight
      C.delta0_pos hm branch).mul_left B0)
  intro k
  exact C.bound x (cmp89NeumannReflectionImage m n k branch)

/-- The complete finite reflection-branch sum is absolutely summable before
the source-order `tsum` is formed. -/
theorem summable_cmp89NeumannRectangularFullGreen_sum
    {fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E}
    {B0 delta0 : ℝ}
    (C : CMP89FullLatticeGreenDecayCertificate fullGreen B0 delta0)
    {m x n : Fin d → ℤ} (hm : ∀ mu, 0 < m mu) :
    Summable (fun k : Fin d → ℤ ↦
      ∑ branch : CMP89NeumannReflectionBranch d,
        fullGreen x (cmp89NeumannReflectionImage m n k branch)) := by
  exact summable_sum fun branch _ ↦
    summable_cmp89NeumannRectangularBranchFullGreen C hm branch

/-- Inserting a common pointwise Green decay into the source-order Neumann
series costs exactly the sealed `2^d` branch multiplicity and the product of
one-dimensional residue constants.  No rectangle-cardinality factor occurs.
-/
theorem norm_cmp89NeumannReflectionSeries_le_of_fullGreenDecay
    {fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E}
    {B0 delta0 : ℝ}
    (C : CMP89FullLatticeGreenDecayCertificate fullGreen B0 delta0)
    {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m) :
    ‖cmp89NeumannReflectionSeries fullGreen m x n‖ ≤
      (2 : ℝ) ^ d * B0 *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta0 * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta0 (x - n)) := by
  let term := fun k : Fin d → ℤ ↦
    ∑ branch : CMP89NeumannReflectionBranch d,
      fullGreen x (cmp89NeumannReflectionImage m n k branch)
  let weight := fun k : Fin d → ℤ ↦
    ∑ branch : CMP89NeumannReflectionBranch d,
      cmp89NeumannRectangularBranchImageWeight delta0 m x n branch k
  have hterm : Summable term :=
    summable_cmp89NeumannRectangularFullGreen_sum C hm
  have hweight : Summable weight :=
    summable_cmp89NeumannRectangularBranchImageWeight_sum C.delta0_pos hm
  have hmajor : Summable (fun k ↦ B0 * weight k) := hweight.mul_left B0
  have hpoint : ∀ k, ‖term k‖ ≤ B0 * weight k := by
    intro k
    calc
      ‖term k‖ ≤
          ∑ branch : CMP89NeumannReflectionBranch d,
            ‖fullGreen x (cmp89NeumannReflectionImage m n k branch)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ branch : CMP89NeumannReflectionBranch d,
          B0 * cmp89NeumannRectangularBranchImageWeight
            delta0 m x n branch k := by
        apply Finset.sum_le_sum
        intro branch _
        exact C.bound x (cmp89NeumannReflectionImage m n k branch)
      _ = B0 * weight k := by
        simp only [weight, Finset.mul_sum]
  have hnorm : Summable (fun k ↦ ‖term k‖) :=
    hmajor.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint
  unfold cmp89NeumannReflectionSeries
  change ‖∑' k, term k‖ ≤ _
  calc
    ‖∑' k, term k‖ ≤ ∑' k, ‖term k‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, B0 * weight k :=
      Summable.tsum_le_tsum hpoint hnorm hmajor
    _ = B0 * ∑' k, weight k := tsum_mul_left
    _ ≤ B0 * ((2 : ℝ) ^ d *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta0 * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta0 (x - n))) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_sum_cmp89NeumannRectangularBranchImageWeight_le
          C.delta0_pos hm hx hn) C.B0_nonneg
    _ = (2 : ℝ) ^ d * B0 *
        ((∏ mu,
            2 / (1 - Real.exp
              (-delta0 * (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight delta0 (x - n)) := by
      ring

/-- Literal full-lattice Green kernel supplied by normalized CMP89 (2.48). -/
def cmp89Eq248PhysicalFullLatticeGreen
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (x y : Fin 4 → ℤ) : ℂ :=
  cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen
    L j mass a (x - y)

/-- The normalized physical Fourier Green constructs the common decay
certificate internally, with literal amplitude `B0` and fine rate
`delta0 = rho / L^j`. -/
def cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass) :
    CMP89FullLatticeGreenDecayCertificate
      (cmp89Eq248PhysicalFullLatticeGreen L j mass a)
      (cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho)
      (rho / ((L ^ j : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft]
    apply mul_nonneg (cmp89Eq248ComplexGreenNumeratorBound_nonneg hrho.le)
    rw [cmp89Eq249CentralStabilizedComplexReciprocalBound]
    exact inv_nonneg.mpr (sub_nonneg.mpr hwindow.le)
  · exact div_pos hrho (by
      exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
  · intro x y
    have hgreen :=
      norm_cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_le_massUniform_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hwindow hmass (x - y)
    rw [cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft
      (L := L) (j := j) rho (x - y)] at hgreen
    simpa [cmp89Eq248PhysicalFullLatticeGreen, mul_comm] using hgreen

/-- Physical specialization of the full rectangular image bound.  The
amplitude, fine decay rate, mass window and both complex strip conditions
remain literal in the theorem signature. -/
theorem norm_cmp89Eq248PhysicalNeumannReflectionSeries_le_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m x n : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m) :
    ‖cmp89NeumannReflectionSeries
        (cmp89Eq248PhysicalFullLatticeGreen L j mass a) m x n‖ ≤
      (2 : ℝ) ^ 4 *
        cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
        ((∏ mu,
            2 / (1 - Real.exp
              (-(rho / ((L ^ j : ℕ) : ℝ)) *
                (cmp89NeumannReflectionPeriodNat m mu : ℝ)))) *
          cmp89SignedLatticeL1ExponentialWeight
            (rho / ((L ^ j : ℕ) : ℝ)) (x - n)) := by
  exact norm_cmp89NeumannReflectionSeries_le_of_fullGreenDecay
    (cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
      ha hrho hamplitude hradius hwindow hmass)
    hm hx hn

end

end YangMills.RG

