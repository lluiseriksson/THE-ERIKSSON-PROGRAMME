import YangMills.RG.BalabanCMP116WilsonHessianDefect

/-!
# Local plaquette operators for the literal Wilson Hessian

Each plaquette second variation is packaged as a canonical continuous
operator on physical one-cochains.  The global Wilson-Hessian operator is
then proved to be the finite sum of these local blocks.  Each block annihilates
cochains vanishing on the plaquette's four physical bonds.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Physical restriction of one local plaquette Hessian as a bounded bilinear
form. -/
noncomputable def physicalWilsonPlaquetteHessianBilinCLM
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun B =>
              ambientWilsonPlaquetteHessian U p
                (physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))
                (physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent B))
            map_add' := fun B C => by
              rw [physicalCochainToSuMatrixTangent_add]
              exact (ambientWilsonPlaquetteHessian U p
                (physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))).map_add _ _
            map_smul' := fun r B => by
              rw [physicalCochainToSuMatrixTangent_smul]
              change ambientWilsonPlaquetteHessian U p
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent A))
                  (r • physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent B)) =
                r • ambientWilsonPlaquetteHessian U p
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent A))
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent B))
              exact (ambientWilsonPlaquetteHessian U p
                (physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))).map_smul r _ }
      map_add' := fun A B => by
        ext C
        rw [physicalCochainToSuMatrixTangent_add]
        exact DFunLike.congr_fun
          ((ambientWilsonPlaquetteHessian U p).map_add
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent B))) _
      map_smul' := fun r A => by
        ext B
        rw [physicalCochainToSuMatrixTangent_smul]
        change ambientWilsonPlaquetteHessian U p
            (r • physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent B)) =
          r • ambientWilsonPlaquetteHessian U p
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent B))
        exact DFunLike.congr_fun
          ((ambientWilsonPlaquetteHessian U p).map_smul r _) _ }

@[simp]
theorem physicalWilsonPlaquetteHessianBilinCLM_apply
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalWilsonPlaquetteHessianBilinCLM U p A B =
      ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) := rfl

/-- Canonical Riesz operator of one local plaquette Hessian. -/
noncomputable def physicalWilsonPlaquetteHessianCLM
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  realBilinearRiesz (physicalWilsonPlaquetteHessianBilinCLM U p)

@[simp]
theorem inner_physicalWilsonPlaquetteHessianCLM
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (physicalWilsonPlaquetteHessianCLM U p A) B =
      ambientWilsonPlaquetteHessian U p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) := by
  rw [physicalWilsonPlaquetteHessianCLM, inner_realBilinearRiesz]
  rfl

/-- A local operator annihilates a cochain vanishing on its four supporting
bonds. -/
theorem physicalWilsonPlaquetteHessianCLM_apply_eq_zero_of_eq_zero_on_support
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (A : PhysicalGaugeOneCochain d N Nc)
    (hA : ∀ b ∈ plaquettePhysicalBondSupport p, A b = 0) :
    physicalWilsonPlaquetteHessianCLM U p A = 0 := by
  apply ext_inner_right ℝ
  intro B
  rw [inner_physicalWilsonPlaquetteHessianCLM, inner_zero_left]
  exact ambientWilsonPlaquetteHessian_eq_zero_of_left_eq_zero_on_support
    U A B p hA

/-- **Plaquette operator decomposition.** The global literal Wilson-Hessian
operator is exactly the finite sum of its local plaquette operators. -/
theorem physicalWilsonHessianCLM_eq_sum_plaquette
    (U : PhysicalGaugeBackground d N Nc) :
    physicalWilsonHessianCLM U =
      ∑ p : ConcretePlaquette d N,
        physicalWilsonPlaquetteHessianCLM U p := by
  apply ContinuousLinearMap.ext
  intro A
  apply ext_inner_right ℝ
  intro B
  rw [inner_physicalWilsonHessianCLM,
    physicalWilsonHessian, ambientWilsonHessian_eq_sum_plaquetteHessian]
  rw [ContinuousLinearMap.sum_apply, sum_inner]
  exact Finset.sum_congr rfl
    (fun p _ => (inner_physicalWilsonPlaquetteHessianCLM U p A B).symm)

/-- Local interacting plaquette defect relative to the trivial background. -/
noncomputable def physicalWilsonPlaquetteHessianDefectCLM
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  physicalWilsonPlaquetteHessianCLM U p -
    physicalWilsonPlaquetteHessianCLM
      (trivialPhysicalGaugeBackground d N Nc) p

@[simp]
theorem inner_physicalWilsonPlaquetteHessianDefectCLM
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (physicalWilsonPlaquetteHessianDefectCLM U p A) B =
      ambientWilsonPlaquetteHessian U p
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A))
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B)) -
      ambientWilsonPlaquetteHessian
          (trivialPhysicalGaugeBackground d N Nc) p
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A))
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B)) := by
  rw [physicalWilsonPlaquetteHessianDefectCLM,
    ContinuousLinearMap.sub_apply, inner_sub_left,
    inner_physicalWilsonPlaquetteHessianCLM,
    inner_physicalWilsonPlaquetteHessianCLM]

/-- A local defect still annihilates cochains vanishing on the plaquette
support. -/
theorem physicalWilsonPlaquetteHessianDefectCLM_apply_eq_zero_of_eq_zero_on_support
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (A : PhysicalGaugeOneCochain d N Nc)
    (hA : ∀ b ∈ plaquettePhysicalBondSupport p, A b = 0) :
    physicalWilsonPlaquetteHessianDefectCLM U p A = 0 := by
  rw [physicalWilsonPlaquetteHessianDefectCLM]
  change physicalWilsonPlaquetteHessianCLM U p A -
      physicalWilsonPlaquetteHessianCLM
        (trivialPhysicalGaugeBackground d N Nc) p A = 0
  rw [
    physicalWilsonPlaquetteHessianCLM_apply_eq_zero_of_eq_zero_on_support
      U p A hA,
    physicalWilsonPlaquetteHessianCLM_apply_eq_zero_of_eq_zero_on_support
      (trivialPhysicalGaugeBackground d N Nc) p A hA,
    sub_zero]

/-- **Local defect decomposition.** The global interacting defect is exactly
the sum of the plaquette defects. -/
theorem physicalWilsonHessianDefectCLM_eq_sum_plaquette
    (U : PhysicalGaugeBackground d N Nc) :
    physicalWilsonHessianDefectCLM U =
      ∑ p : ConcretePlaquette d N,
        physicalWilsonPlaquetteHessianDefectCLM U p := by
  rw [physicalWilsonHessianDefectCLM,
    physicalWilsonHessianCLM_eq_sum_plaquette U,
    physicalWilsonHessianCLM_eq_sum_plaquette
      (trivialPhysicalGaugeBackground d N Nc)]
  simpa only [physicalWilsonPlaquetteHessianDefectCLM] using
    (Finset.sum_sub_distrib
      (s := Finset.univ)
      (fun p : ConcretePlaquette d N =>
        physicalWilsonPlaquetteHessianCLM U p)
      (fun p : ConcretePlaquette d N =>
        physicalWilsonPlaquetteHessianCLM
          (trivialPhysicalGaugeBackground d N Nc) p)).symm

end

end YangMills.RG
