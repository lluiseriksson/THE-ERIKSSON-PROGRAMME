import YangMills.RG.BalabanCMP116FourFactorMixedLipschitz
import YangMills.RG.BalabanCMP116MatrixTraceL2OpNorm
import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixedBounds
import YangMills.RG.BalabanCMP116WilsonPlaquetteMixedFormula

/-!
# Bilinear small-background bound for one Wilson plaquette

The sixteen-term abstract estimate is instantiated with the four oriented
edges of a physical plaquette.  The resulting constant is independent of the
lattice volume and preserves one factor from each variation direction.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The mixed plaquette holonomy is bilinear-Lipschitz around the trivial
background, with an explicit dimension-free matrix constant. -/
theorem norm_orientedPlaquetteHolonomyMixedVariation_sub_trivial_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N)
    (LA LB : ℝ) (hLA : 0 ≤ LA) (hLB : 0 ≤ LB)
    (hA : ∀ k : Fin 4, ‖orientedWilsonGenerator A (p.edges k)‖ ≤ LA)
    (hB : ∀ k : Fin 4, ‖orientedWilsonGenerator B (p.edges k)‖ ≤ LB) :
    ‖orientedPlaquetteHolonomyMixedVariation U A B p -
        orientedPlaquetteHolonomyMixedVariation
          (trivialPhysicalGaugeBackground d N Nc) A B p‖ ≤
      64 * ε * LA * LB := by
  apply norm_fourFactorMixed_sub_le
    (fun k => orientedWilsonBackgroundFactor U (p.edges k))
    (fun k => orientedWilsonBackgroundFactor
      (trivialPhysicalGaugeBackground d N Nc) (p.edges k))
    (orientedPlaquetteFactorFirst U A p)
    (orientedPlaquetteFactorFirst
      (trivialPhysicalGaugeBackground d N Nc) A p)
    (orientedPlaquetteFactorFirst U B p)
    (orientedPlaquetteFactorFirst
      (trivialPhysicalGaugeBackground d N Nc) B p)
    (orientedPlaquetteFactorMixedSecond U A B p)
    (orientedPlaquetteFactorMixedSecond
      (trivialPhysicalGaugeBackground d N Nc) A B p)
    LA LB ε hLA hLB hε
  · intro k
    rw [norm_orientedWilsonBackgroundFactor]
  · intro k
    rw [norm_orientedWilsonBackgroundFactor]
  · intro k
    simpa using
      norm_orientedWilsonBackgroundFactor_sub_trivial_le
        U ε hsmall (p.edges k)
  · intro k
    change ‖orientedWilsonFactorFirst U A (p.edges k) 0‖ ≤ LA
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_le U A (p.edges k)) (hA k)
  · intro k
    change
      ‖orientedWilsonFactorFirst
        (trivialPhysicalGaugeBackground d N Nc) A (p.edges k) 0‖ ≤ LA
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_le
        (trivialPhysicalGaugeBackground d N Nc) A (p.edges k)) (hA k)
  · intro k
    change
      ‖orientedWilsonFactorFirst U A (p.edges k) 0 -
          orientedWilsonFactorFirst
            (trivialPhysicalGaugeBackground d N Nc) A (p.edges k) 0‖ ≤
        ε * LA
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_sub_trivial_le
        U ε hsmall A (p.edges k))
      (mul_le_mul_of_nonneg_left (hA k) hε)
  · intro k
    change ‖orientedWilsonFactorFirst U B (p.edges k) 0‖ ≤ LB
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_le U B (p.edges k)) (hB k)
  · intro k
    change
      ‖orientedWilsonFactorFirst
        (trivialPhysicalGaugeBackground d N Nc) B (p.edges k) 0‖ ≤ LB
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_le
        (trivialPhysicalGaugeBackground d N Nc) B (p.edges k)) (hB k)
  · intro k
    change
      ‖orientedWilsonFactorFirst U B (p.edges k) 0 -
          orientedWilsonFactorFirst
            (trivialPhysicalGaugeBackground d N Nc) B (p.edges k) 0‖ ≤
        ε * LB
    exact le_trans
      (norm_orientedWilsonFactorFirst_zero_sub_trivial_le
        U ε hsmall B (p.edges k))
      (mul_le_mul_of_nonneg_left (hB k) hε)
  · intro k
    change
      ‖orientedWilsonFactorMixedSecond U A B (p.edges k)‖ ≤ LA * LB
    exact le_trans
      (norm_orientedWilsonFactorMixedSecond_le U A B (p.edges k))
      (mul_le_mul (hA k) (hB k) (norm_nonneg _) hLA)
  · intro k
    change
      ‖orientedWilsonFactorMixedSecond
        (trivialPhysicalGaugeBackground d N Nc) A B (p.edges k)‖ ≤
        LA * LB
    exact le_trans
      (norm_orientedWilsonFactorMixedSecond_le
        (trivialPhysicalGaugeBackground d N Nc) A B (p.edges k))
      (mul_le_mul (hA k) (hB k) (norm_nonneg _) hLA)
  · intro k
    change
      ‖orientedWilsonFactorMixedSecond U A B (p.edges k) -
          orientedWilsonFactorMixedSecond
            (trivialPhysicalGaugeBackground d N Nc) A B (p.edges k)‖ ≤
        ε * (LA * LB)
    exact le_trans
      (norm_orientedWilsonFactorMixedSecond_sub_trivial_le
        U ε hε hsmall A B (p.edges k))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul (hA k) (hB k) (norm_nonneg _) hLA) hε)

/-- Scalar local Hessian bound.  The only dimension-dependent local factor is
the trace cost `Nc`; there is still no lattice-volume factor. -/
theorem abs_orientedWilsonPlaquetteDirectMixedFormula_sub_trivial_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N)
    (LA LB : ℝ) (hLA : 0 ≤ LA) (hLB : 0 ≤ LB)
    (hA : ∀ k : Fin 4, ‖orientedWilsonGenerator A (p.edges k)‖ ≤ LA)
    (hB : ∀ k : Fin 4, ‖orientedWilsonGenerator B (p.edges k)‖ ≤ LB) :
    |orientedWilsonPlaquetteDirectMixedFormula U A B p -
        orientedWilsonPlaquetteDirectMixedFormula
          (trivialPhysicalGaugeBackground d N Nc) A B p| ≤
      (Nc : ℝ) * (64 * ε * LA * LB) := by
  let M :=
    orientedPlaquetteHolonomyMixedVariation U A B p
  let M' :=
    orientedPlaquetteHolonomyMixedVariation
      (trivialPhysicalGaugeBackground d N Nc) A B p
  have hmatrix : ‖M - M'‖ ≤ 64 * ε * LA * LB := by
    exact norm_orientedPlaquetteHolonomyMixedVariation_sub_trivial_le
      U ε hε hsmall A B p LA LB hLA hLB hA hB
  have htrace := abs_ambientTraceReal_le_card_mul_norm (M - M')
  have hformula :
      |orientedWilsonPlaquetteDirectMixedFormula U A B p -
          orientedWilsonPlaquetteDirectMixedFormula
            (trivialPhysicalGaugeBackground d N Nc) A B p| =
        |ambientTraceReal (M - M')| := by
    unfold orientedWilsonPlaquetteDirectMixedFormula
    simp only [M, M', ambientTraceReal, Matrix.sub_apply, Complex.sub_re,
      Finset.sum_sub_distrib]
    ring_nf
    rw [abs_sub_comm]
    congr 1 <;> ring
  rw [hformula]
  exact le_trans htrace
    (mul_le_mul_of_nonneg_left hmatrix (Nat.cast_nonneg Nc))

end

end YangMills.RG
