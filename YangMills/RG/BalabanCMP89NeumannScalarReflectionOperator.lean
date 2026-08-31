import YangMills.RG.BalabanCMP89NeumannReflectionRepresentation
import YangMills.RG.FinitePiLpCombesThomas

/-!
# Compiler-verified operator assembled from the CMP89 scalar reflection kernel

Cold-sealed at source checkpoint `cdd859ba99671e83a1ef2b3d8119a4e376a97ced`;
see Verification Ledger Addendum 1003.

This module turns the literal scalar multiple-reflection series into a
finite-carrier continuous linear operator. The construction is internal: a
later producer may identify it with the canonical regional Green by proving
one inverse law for the literal regional precision. No reflection identity is
assumed here.
-/

namespace YangMills.RG

noncomputable section

variable {ι g : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- Finite counting-Hilbert operator assembled from one scalar kernel. -/
noncomputable def finitePiLpScalarKernelOperator
    (kernel : ι → ι → ℝ) :
    FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun target =>
        ∑ source, kernel target source • f source
      map_add' := fun f h => by
        apply PiLp.ext
        intro target
        change
          (∑ source, kernel target source • (f source + h source)) =
            (∑ source, kernel target source • f source) +
              ∑ source, kernel target source • h source
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro source _
        exact smul_add _ _ _
      map_smul' := fun c f => by
        apply PiLp.ext
        intro target
        change
          (∑ source, kernel target source • (c • f source)) =
            c • ∑ source, kernel target source • f source
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro source _
        exact smul_comm _ _ _ }

/-- A single-site probe reads exactly one entry of the assembled scalar
kernel. -/
@[simp] theorem finitePiLpScalarKernelOperator_single
    (kernel : ι → ι → ℝ) (source target : ι) (v : g) :
    finitePiLpScalarKernelOperator (g := g) kernel
        (singleFinitePiLp source v) target =
      kernel target source • v := by
  classical
  change
    (∑ x, kernel target x • (if x = source then v else 0)) =
      kernel target source • v
  simp

variable {d : ℕ}

/-- Scalar reflection kernel transported from the source rectangle to a
finite regional carrier by one explicit site equivalence. -/
def cmp89NeumannScalarReflectionKernel
    {m : Fin d → ℤ}
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃ ι)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (target source : ι) : ℝ :=
  cmp89NeumannReflectionSeries fullGreen m
    (siteEquiv.symm target).1 (siteEquiv.symm source).1

/-- Continuous finite-carrier operator whose entries are the literal CMP89
multiple-reflection series. -/
noncomputable def cmp89NeumannScalarReflectionOperator
    {m : Fin d → ℤ}
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃ ι)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) :
    FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g :=
  finitePiLpScalarKernelOperator
    (cmp89NeumannScalarReflectionKernel siteEquiv fullGreen)

/-- Entry formula for the internally assembled reflection operator. -/
theorem cmp89NeumannScalarReflectionOperator_single
    {m : Fin d → ℤ}
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃ ι)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) (v : g) :
    cmp89NeumannScalarReflectionOperator (g := g) siteEquiv fullGreen
        (singleFinitePiLp (siteEquiv n) v) (siteEquiv x) =
      cmp89NeumannReflectionSeries fullGreen m x.1 n.1 • v := by
  simp [cmp89NeumannScalarReflectionOperator,
    cmp89NeumannScalarReflectionKernel]

/-- The vector-valued reflection series for a scalar action is the scalar
reflection series acting on the fibre vector. Absolute summability is kept
visible because it is the analytic input that makes the `tsum` transport
valid. -/
theorem cmp89NeumannReflectionSeries_smul
    {m x n : Fin d → ℤ}
    {fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    (hsummable : Summable (fun k : Fin d → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch d,
        fullGreen x (cmp89NeumannReflectionImage m n k branch)))
    (v : g) :
    cmp89NeumannReflectionSeries
        (fun y z => fullGreen y z • v) m x n =
      cmp89NeumannReflectionSeries fullGreen m x n • v := by
  unfold cmp89NeumannReflectionSeries
  have hterm : (fun k : Fin d → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch d,
        fullGreen x (cmp89NeumannReflectionImage m n k branch) • v) =
      (fun k : Fin d → ℤ =>
        (∑ branch : CMP89NeumannReflectionBranch d,
          fullGreen x (cmp89NeumannReflectionImage m n k branch)) • v) := by
    funext k
    rw [Finset.sum_smul]
  rw [hterm]
  exact hsummable.tsum_smul_const v

end

end YangMills.RG
