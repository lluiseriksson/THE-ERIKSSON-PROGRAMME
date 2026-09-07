import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian

/-!
# CMP99 (3.51)--(3.54): local analytic Laplacian perturbation

The source term `V'_1(A)` is not accepted as an operator parameter.  It is
the literal difference of the two analytic covariant stencils, expanded
before any norm estimate into the forward-difference change and the two
backward inverse-transport terms.  All three terms use the same Dirichlet
extension and the same bond orientation as the two regional Laplacians.

This is the exact local operator identity only.  Producing the printed
`O(alpha1)` bound of (3.54) from the Eq. (3.37) domain remains open.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal local `V'_1(A)` between two analytic backgrounds.  The three
summands are kept separate so their source estimates cannot be hidden in one
caller-supplied budget. -/
noncomputable def cmp99Eq360ComplexLocalLaplacianPerturbation
    (Omega : ActiveGaugeRegion d N)
    (U0 U1 : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) →L[ℂ]
      ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi =>
        let extended := cmp99Eq360ComplexDirichletExtend Omega phi
        WithLp.toLp 2 fun x =>
          ((spacing : ℂ)⁻¹) •
            ∑ i : Fin d,
              ((cmp99Eq360ComplexCovariantDifference U0 spacing extended
                    (x.1, i) -
                  cmp99Eq360ComplexCovariantDifference U1 spacing extended
                    (x.1, i)) -
                cmp99SpecialLinearAdjointCoordLM
                  (U0 (positiveEdgeOfPhysicalBond
                    ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
                  (cmp99Eq360ComplexCovariantDifference U0 spacing extended
                    (x.1.shiftBack i, i)) +
                cmp99SpecialLinearAdjointCoordLM
                  (U1 (positiveEdgeOfPhysicalBond
                    ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
                  (cmp99Eq360ComplexCovariantDifference U1 spacing extended
                    (x.1.shiftBack i, i)))
      map_add' := fun phi psi => by
        apply PiLp.ext
        intro x
        simp only [cmp99Eq360ComplexDirichletExtend_add,
          cmp99Eq360ComplexCovariantDifference_add, map_add, PiLp.add_apply]
        rw [← smul_add]
        apply congrArg (((spacing : ℂ)⁻¹) • ·)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        module
      map_smul' := fun c phi => by
        apply PiLp.ext
        intro x
        simp only [cmp99Eq360ComplexDirichletExtend_smul,
          cmp99Eq360ComplexCovariantDifference_smul, map_smul,
          Finset.smul_sum, smul_sub, smul_add, smul_smul, PiLp.smul_apply]
        simp only [RingHom.id_apply, mul_comm] }

@[simp] theorem cmp99Eq360ComplexLocalLaplacianPerturbation_apply
    (Omega : ActiveGaugeRegion d N)
    (U0 U1 : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99Eq360ComplexLocalLaplacianPerturbation Omega U0 U1 spacing phi x =
      let extended := cmp99Eq360ComplexDirichletExtend Omega phi
      ((spacing : ℂ)⁻¹) •
        ∑ i : Fin d,
          ((cmp99Eq360ComplexCovariantDifference U0 spacing extended
                (x.1, i) -
              cmp99Eq360ComplexCovariantDifference U1 spacing extended
                (x.1, i)) -
            cmp99SpecialLinearAdjointCoordLM
              (U0 (positiveEdgeOfPhysicalBond
                ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
              (cmp99Eq360ComplexCovariantDifference U0 spacing extended
                (x.1.shiftBack i, i)) +
            cmp99SpecialLinearAdjointCoordLM
              (U1 (positiveEdgeOfPhysicalBond
                ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
              (cmp99Eq360ComplexCovariantDifference U1 spacing extended
                (x.1.shiftBack i, i))) :=
  rfl

/-- The expanded local operator is exactly the difference of the two
regional analytic Laplacians. -/
theorem cmp99Eq360_complexRegionalLaplacian_sub_eq_localPerturbation
    (Omega : ActiveGaugeRegion d N)
    (U0 U1 : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ) :
    cmp99Eq360ComplexRegionalLaplacian Omega U0 spacing -
        cmp99Eq360ComplexRegionalLaplacian Omega U1 spacing =
      cmp99Eq360ComplexLocalLaplacianPerturbation Omega U0 U1 spacing := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  change
    cmp99Eq360ComplexRegionalLaplacian Omega U0 spacing phi x -
        cmp99Eq360ComplexRegionalLaplacian Omega U1 spacing phi x =
      cmp99Eq360ComplexLocalLaplacianPerturbation Omega U0 U1 spacing phi x
  rw [cmp99Eq360ComplexRegionalLaplacian_apply,
    cmp99Eq360ComplexRegionalLaplacian_apply,
    cmp99Eq360ComplexLocalLaplacianPerturbation_apply]
  rw [← smul_sub]
  apply congrArg (((spacing : ℂ)⁻¹) • ·)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  module

/-- Source orientation of (3.53): perturbed equals baseline minus the
internally constructed local perturbation. -/
theorem cmp99Eq360_complexRegionalLaplacian_eq_sub_localPerturbation
    (Omega : ActiveGaugeRegion d N)
    (U0 U1 : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (spacing : ℝ) :
    cmp99Eq360ComplexRegionalLaplacian Omega U1 spacing =
      cmp99Eq360ComplexRegionalLaplacian Omega U0 spacing -
        cmp99Eq360ComplexLocalLaplacianPerturbation Omega U0 U1 spacing := by
  have h := cmp99Eq360_complexRegionalLaplacian_sub_eq_localPerturbation
    Omega U0 U1 spacing
  rw [← h]
  abel

end

end YangMills.RG
