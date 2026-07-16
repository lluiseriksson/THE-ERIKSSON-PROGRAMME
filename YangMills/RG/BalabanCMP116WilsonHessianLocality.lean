import YangMills.RG.BalabanCMP116WilsonHessianFlatPrecision
import YangMills.RG.PhysicalShellLocalityD1

/-!
# Exact locality of the interacting Wilson Hessian

The Wilson Hessian at a nontrivial background remains a sum of plaquette
Hessians.  This module proves the exact support statement needed before any
small-background estimate:

* a plaquette Hessian vanishes if either tangent is zero on the four physical
  bonds of that plaquette;
* consequently, matrix elements between single-bond probes at physical bond
  distance greater than two vanish at every background.

This is a structural interacting-background result.  It uses the literal
unitary variation and does not assume a kernel estimate or a random-walk
expansion.
-/

namespace YangMills.RG

open Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The older physical-support definition and the four explicit bond slots
used by the shell calculus are literally the same finite set. -/
theorem physicalBondOfEdge_edges_eq_plaquetteBondSlots
    (p : ConcretePlaquette d N) (k : Fin 4) :
    physicalBondOfEdge (p.edges k) = plaquetteBondSlots p k := by
  fin_cases k <;> rfl

theorem mem_plaquettePhysicalBondSupport_iff
    (p : ConcretePlaquette d N) (b : PhysicalBond d N) :
    b ∈ plaquettePhysicalBondSupport p ↔
      ∃ k : Fin 4, plaquetteBondSlots p k = b := by
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨k, hk, hkb⟩
    exact ⟨k, by
      rw [← physicalBondOfEdge_edges_eq_plaquetteBondSlots p k]
      exact hkb⟩
  · rintro ⟨k, hk⟩
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_univ k, by
      rw [physicalBondOfEdge_edges_eq_plaquetteBondSlots p k]
      exact hk⟩

/-- If the first cochain vanishes at a physical bond, the concrete
two-parameter exponential increment there is independent of `t`. -/
theorem physicalSuUnitaryIncrement_t_independent_of_eq_zero
    (A B : PhysicalGaugeOneCochain d N Nc)
    (b : PhysicalBond d N)
    (hA : A b = 0) (t s : ℝ) :
    physicalSuUnitaryIncrement
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B) b t s =
      physicalSuUnitaryIncrement
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B) b 0 s := by
  apply Subtype.ext
  change physicalMatrixExp
      (t • ((suLieCoordIso Nc).symm (A b)).toMatrix
        + s • ((suLieCoordIso Nc).symm (B b)).toMatrix) =
    physicalMatrixExp
      ((0 : ℝ) • ((suLieCoordIso Nc).symm (A b)).toMatrix
        + s • ((suLieCoordIso Nc).symm (B b)).toMatrix)
  rw [hA]
  have hz : ((suLieCoordIso Nc).symm (0 : SUNLieCoord Nc)).toMatrix = 0 := by
    rw [(suLieCoordIso Nc).symm.map_zero]
    rfl
  rw [hz]
  congr 1
  module

/-- Local physical unitary variation equals the local ambient Fréchet
Hessian. -/
theorem physicalPlaquetteWilsonMixedVariationUnitary_eq_ambientHessian
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) :
    physicalPlaquetteWilsonMixedVariationUnitary U X Y p =
      ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient X)
        (physicalSuTangentToAmbient Y) := by
  unfold physicalPlaquetteWilsonMixedVariationUnitary
  unfold plaquetteWilsonMixedVariation
  have hcurve :
      (fun t => deriv (fun s =>
        plaquetteWilsonVariation unitaryWilsonPlaquetteEnergy
          (physicalBackgroundToUnitary U)
          (physicalSuUnitaryIncrement X Y) p t s) 0) =
      (fun t => deriv (fun s =>
        ambientWilsonPlaquetteAction U
          (physicalTwoParameterAmbientTangent X Y t s) p) 0) := by
    funext t
    congr 1
    funext s
    exact
      (ambientWilsonPlaquetteAction_twoParameter_eq_unitaryVariation
        U X Y p t s).symm
  rw [hcurve]
  simpa only [physicalTwoParameterAmbientTangent,
    physicalSuTangentToAmbient, ambientWilsonPlaquetteHessian,
    Pi.add_apply, Pi.smul_apply] using
    nested_deriv_line_eq_sndFDeriv
      (fun Z => ambientWilsonPlaquetteAction U Z p)
      (fun Z => analyticAt_ambientWilsonPlaquetteAction U Z p)
      (physicalSuTangentToAmbient X)
      (physicalSuTangentToAmbient Y)

/-- A local Wilson plaquette Hessian vanishes when its first cochain direction
is zero on the four supporting bonds. -/
theorem ambientWilsonPlaquetteHessian_eq_zero_of_left_eq_zero_on_support
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N)
    (hA : ∀ b ∈ plaquettePhysicalBondSupport p, A b = 0) :
    ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) = 0 := by
  rw [← physicalPlaquetteWilsonMixedVariationUnitary_eq_ambientHessian]
  apply plaquetteWilsonMixedVariation_eq_zero_of_t_independent_on_support
  intro b hb t s
  exact physicalSuUnitaryIncrement_t_independent_of_eq_zero
    A B b (hA b hb) t s

/-- Symmetric right-support version of the local vanishing theorem. -/
theorem ambientWilsonPlaquetteHessian_eq_zero_of_right_eq_zero_on_support
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N)
    (hB : ∀ b ∈ plaquettePhysicalBondSupport p, B b = 0) :
    ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) = 0 := by
  rw [ambientWilsonPlaquetteHessian_symm]
  exact ambientWilsonPlaquetteHessian_eq_zero_of_left_eq_zero_on_support
    U B A p hB

/-- Single-bond cochains vanish on a plaquette support that misses their
source bond. -/
theorem singlePhysicalBondCochain_eq_zero_on_plaquetteSupport
    (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (π : ConcretePlaquette d N)
    (hp : p ∉ plaquettePhysicalBondSupport π) :
    ∀ b ∈ plaquettePhysicalBondSupport π,
      singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v b = 0 := by
  intro b hb
  exact singlePhysicalBondCochain_of_ne v (by
    intro hbp
    subst hbp
    exact hp hb)

/-- **WIL-H4 structural locality.** At every physical background, Wilson
Hessian matrix elements between bond probes at distance greater than two
vanish exactly. -/
theorem physicalWilsonHessian_single_eq_zero_of_dist_gt_two
    (U : PhysicalGaugeBackground d N Nc)
    (p q : PhysicalBond d N)
    (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    physicalWilsonHessian U
        (physicalCochainToSuMatrixTangent
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v))
        (physicalCochainToSuMatrixTangent
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [physicalWilsonHessian, ambientWilsonHessian_eq_sum_plaquetteHessian]
  apply Finset.sum_eq_zero
  intro π hπ
  by_cases hp : p ∈ plaquettePhysicalBondSupport π
  · by_cases hq : q ∈ plaquettePhysicalBondSupport π
    · rcases (mem_plaquettePhysicalBondSupport_iff π p).mp hp with ⟨k, hk⟩
      rcases (mem_plaquettePhysicalBondSupport_iff π q).mp hq with ⟨l, hl⟩
      exfalso
      have hd : physicalBondDist q p ≤ 2 := by
        rw [← hk, ← hl]
        exact plaquetteBondSlots_dist_le π l k
      omega
    · exact ambientWilsonPlaquetteHessian_eq_zero_of_right_eq_zero_on_support
        U _ _ π
        (singlePhysicalBondCochain_eq_zero_on_plaquetteSupport q w π hq)
  · exact ambientWilsonPlaquetteHessian_eq_zero_of_left_eq_zero_on_support
      U _ _ π
      (singlePhysicalBondCochain_eq_zero_on_plaquetteSupport p v π hp)

end

end YangMills.RG
