import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision
import YangMills.RG.PhysicalGaugeFlatPoincare

/-!
# Fixed-region existence gate for the CMP89 Neumann Poincare constant

Compiler-verified in a fresh Colab checkout at source checkpoint
`a1fe7d151400d99fe0d89e5d430ddb992a6168b8`.

This brick reduces existence of a finite-volume Neumann Poincare constant to
the exact joint-kernel statement for the same internal-bond derivative and the
same averaging operator.  It deliberately proves no bound uniform in the
region, depth or block ratio: the quantitative `CP` needed downstream still
requires source geometry.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Exact fixed-region kernel gate: covariantly constant Neumann modes killed
by the retained average are zero. -/
def CMP89SourceNeumannRegionalJointKernelTrivial
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing : ℝ) : Prop :=
  ∀ phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc),
    cmp89SourceNeumannRegionalCovariantD0CLM
        Omega rho U spacing phi = 0 →
      Qprime phi = 0 → phi = 0

/-- Finite-dimensional compactness produces some positive Poincare constant
from the literal two-map joint-kernel theorem.  No uniform numerical control
of that constant is claimed. -/
theorem exists_cmp89SourceNeumannRegionalPoincare_of_jointKernel
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] F)
    (spacing : ℝ)
    (hjoint : CMP89SourceNeumannRegionalJointKernelTrivial
      Omega rho U Qprime spacing) :
    ∃ CP : ℝ, 0 < CP ∧
      CMP89SourceNeumannRegionalPoincare
        Omega rho U Qprime spacing CP := by
  let D := cmp89SourceNeumannRegionalCovariantD0CLM
    Omega rho U spacing
  let Z : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ] ℝ := 0
  obtain ⟨CP, hCP, hbound⟩ :=
    exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial D Qprime Z
      (by
        intro phi hD hQ _hZ
        exact hjoint phi hD hQ)
  refine ⟨CP, hCP, ?_⟩
  intro phi
  simpa [CMP89SourceNeumannRegionalPoincare, D, Z] using hbound phi

variable {M depth : ℕ} [NeZero M]
variable {Omega : ActiveGaugeRegion d N}
variable {rho : SUNAdjointModel Nc} {spacing : ℝ}
variable {background : GaugeConfig d N (SUN Nc)}

/-- Joint-kernel gate pinned to the literal retained `Q'_r`. -/
def CMP89SourceRetainedNeumannPrefixJointKernelTrivial
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (r : CMP85PositivePrefix depth) : Prop :=
  CMP89SourceNeumannRegionalJointKernelTrivial Omega rho background
    (T.towerAt r.1).Qprime spacing

/-- Fixed-prefix Poincare existence with no free average operator. -/
theorem exists_cmp89SourceRetainedNeumannPrefixPoincare_of_jointKernel
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (r : CMP85PositivePrefix depth)
    (hjoint : CMP89SourceRetainedNeumannPrefixJointKernelTrivial T r) :
    ∃ CP : ℝ, 0 < CP ∧
      CMP89SourceRetainedNeumannPrefixPoincare T r CP := by
  exact exists_cmp89SourceNeumannRegionalPoincare_of_jointKernel
    Omega rho background (T.towerAt r.1).Qprime spacing hjoint

end

end YangMills.RG
