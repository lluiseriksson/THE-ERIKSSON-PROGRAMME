import YangMills.RG.FinitePiLpPointSourceRightInverse
import YangMills.RG.BalabanCMP89NeumannMassReflection
import YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies

/-!
# DRAFT: point-source three-species form of the CMP89 Neumann inverse gate

This scratch module reduces the exact regional right-inverse equation to its
literal point-source form and rewrites only the bare-mass species through the
multiple-reflection operator.  The Laplacian and generated `Q′*Q′` actions
remain physical expressions, not supplied kernels or renamed conclusions.

No source module is promoted from this draft until the mass, three-species
and physical reflection parents have compiler evidence.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The complete regional right-inverse equation is equivalent to the exact
point-source sum of the Neumann Laplacian, the internally transported bare
mass species, and the generated adjoint-average species. -/
theorem cmp89SourceNeumannRegionalGaugePrecision_comp_reflection_eq_id_iff_pointSource_threeSpecies
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m : Fin d → ℤ}
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing mass a : ℝ)
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) :
    (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a).comp
          (cmp89NeumannScalarReflectionOperator
            (g := SUNLieCoord Nc) siteEquiv fullGreen) =
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) ↔
      ∀ source v,
        cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (cmp89NeumannScalarReflectionOperator
                (g := SUNLieCoord Nc) siteEquiv fullGreen
                (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (cmp89NeumannScalarReflectionOperator
                (g := SUNLieCoord Nc) siteEquiv fullGreen
                (singleFinitePiLp source v)) =
          singleFinitePiLp source v := by
  let G := cmp89NeumannScalarReflectionOperator
    (g := SUNLieCoord Nc) siteEquiv fullGreen
  constructor
  · intro h source v
    have hpoint :=
      (finitePiLp_comp_eq_id_iff_pointSources
        (cmp89SourceNeumannRegionalGaugePrecision
          Omega rho U Qprime spacing mass a) G).mp h source v
    have hsplit :
        cmp89SourceNeumannRegionalGaugePrecision
              Omega rho U Qprime spacing mass a
              (G (singleFinitePiLp source v)) =
            cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
                (G (singleFinitePiLp source v)) +
              (mass ^ 2 • ContinuousLinearMap.id ℝ
                (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
                (G (singleFinitePiLp source v)) +
              (a • (Qprime.adjoint.comp Qprime))
                (G (singleFinitePiLp source v)) := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply] using congrArg
        (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
          T (singleFinitePiLp source v))
        (cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies
          Omega rho U Qprime spacing mass a G)
    have hmass :
        (mass ^ 2 • ContinuousLinearMap.id ℝ
            (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
            (G (singleFinitePiLp source v)) =
          cmp89NeumannScalarReflectionOperator
            (g := SUNLieCoord Nc) siteEquiv
            (fun y z => mass ^ 2 * fullGreen y z)
            (singleFinitePiLp source v) := by
      simpa only [ContinuousLinearMap.comp_apply] using congrArg
        (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
          T (singleFinitePiLp source v))
        (mass_sq_comp_cmp89NeumannScalarReflectionOperator
          mass siteEquiv fullGreen)
    calc
      cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) =
          cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            (mass ^ 2 • ContinuousLinearMap.id ℝ
              (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
              (G (singleFinitePiLp source v)) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) := by rw [hmass]
      _ = cmp89SourceNeumannRegionalGaugePrecision
            Omega rho U Qprime spacing mass a
            (G (singleFinitePiLp source v)) := hsplit.symm
      _ = singleFinitePiLp source v := hpoint
  · intro h
    apply (finitePiLp_comp_eq_id_iff_pointSources
      (cmp89SourceNeumannRegionalGaugePrecision
        Omega rho U Qprime spacing mass a) G).mpr
    intro source v
    have hsplit :
        cmp89SourceNeumannRegionalGaugePrecision
              Omega rho U Qprime spacing mass a
              (G (singleFinitePiLp source v)) =
            cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
                (G (singleFinitePiLp source v)) +
              (mass ^ 2 • ContinuousLinearMap.id ℝ
                (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
                (G (singleFinitePiLp source v)) +
              (a • (Qprime.adjoint.comp Qprime))
                (G (singleFinitePiLp source v)) := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply] using congrArg
        (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
          T (singleFinitePiLp source v))
        (cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies
          Omega rho U Qprime spacing mass a G)
    have hmass :
        (mass ^ 2 • ContinuousLinearMap.id ℝ
            (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
            (G (singleFinitePiLp source v)) =
          cmp89NeumannScalarReflectionOperator
            (g := SUNLieCoord Nc) siteEquiv
            (fun y z => mass ^ 2 * fullGreen y z)
            (singleFinitePiLp source v) := by
      simpa only [ContinuousLinearMap.comp_apply] using congrArg
        (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) =>
          T (singleFinitePiLp source v))
        (mass_sq_comp_cmp89NeumannScalarReflectionOperator
          mass siteEquiv fullGreen)
    calc
      cmp89SourceNeumannRegionalGaugePrecision
            Omega rho U Qprime spacing mass a
            (G (singleFinitePiLp source v)) =
          cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            (mass ^ 2 • ContinuousLinearMap.id ℝ
              (ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)))
              (G (singleFinitePiLp source v)) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) := hsplit
      _ = cmp89SourceNeumannRegionalLaplacian Omega rho U spacing
              (G (singleFinitePiLp source v)) +
            cmp89NeumannScalarReflectionOperator
              (g := SUNLieCoord Nc) siteEquiv
              (fun y z => mass ^ 2 * fullGreen y z)
              (singleFinitePiLp source v) +
            (a • (Qprime.adjoint.comp Qprime))
              (G (singleFinitePiLp source v)) := by rw [hmass]
      _ = singleFinitePiLp source v := h source v

end

end YangMills.RG
