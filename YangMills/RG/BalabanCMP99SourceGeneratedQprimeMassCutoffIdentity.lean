/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision
import YangMills.RG.FinitePiLpScalarCommutator

/-!
# PRE-VALIDATION: the normalized `Q'^* Q'` species in CMP99 (3.88)

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP99 (3.88), printed p. 409, fixes one output site and writes the mass part
of `K(h) = h Delta'_a - Delta'_a h` as a sum over input sites.  This file
derives that sum from the literal generated `Q'` tower.  The normalization is
the already generated mass coefficient; neither the kernel nor the
coefficient is supplied independently by the caller.

This is the third algebraic species of (3.88).  Combining it with the two
ambient covariant-Laplacian species still requires the explicit regional
compression dictionary; no physical `norm R' < 1` estimate is asserted here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Exact fixed-output expansion of a scalar commutator on an arbitrary
finite counting-Hilbert field. -/
theorem finitePiLpScalarCommutator_apply_eq_sum
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (phi : FinitePiLpField ι g) (target : ι) :
    finitePiLpScalarCommutator h A phi target =
      ∑ source : ι,
        (h target - h source) •
          A (singleFinitePiLp source (phi source)) target := by
  have hdecomp : phi =
      ∑ source : ι, singleFinitePiLp source (phi source) :=
    (sum_singleFinitePiLp_eq phi).symm
  calc
    finitePiLpScalarCommutator h A phi target =
        finitePiLpScalarCommutator h A
          (∑ source : ι, singleFinitePiLp source (phi source)) target :=
      congrArg (fun f => finitePiLpScalarCommutator h A f target) hdecomp
    _ = (∑ source : ι,
          finitePiLpScalarCommutator h A
            (singleFinitePiLp source (phi source))) target := by
      rw [map_sum]
    _ = ∑ source : ι,
          finitePiLpScalarCommutator h A
            (singleFinitePiLp source (phi source)) target :=
      finitePiLp_sum_apply _ _ _
    _ = ∑ source : ι,
          (h target - h source) •
            A (singleFinitePiLp source (phi source)) target := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact finitePiLpScalarCommutator_single_apply h A source target
        (phi source)

/-- Scalar commutators preserve literal operator addition before any
estimate combines the two row budgets. -/
theorem finitePiLpScalarCommutator_add
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (A B : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpScalarCommutator h (A + B) =
      finitePiLpScalarCommutator h A + finitePiLpScalarCommutator h B := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [finitePiLpScalarCommutator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add]
  module

/-- A real mass coefficient factors exactly out of the scalar commutator. -/
theorem finitePiLpScalarCommutator_smul
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ) (a : ℝ)
    (A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpScalarCommutator h (a • A) =
      a • finitePiLpScalarCommutator h A := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [finitePiLpScalarCommutator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_smul]
  module

/-- Exact third-species split for a source precision
`Delta'_a = Delta_U + a Q'^* Q'`.  The complete mass contribution is the
literal fixed-output kernel sum, with `a` still visible. -/
theorem finitePiLpScalarCommutator_sourceGaugePrecision_apply_eq
    {ι κ g : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (h : ι → ℝ)
    (covariantLaplacian : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (Qprime : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (a : ℝ) (phi : FinitePiLpField ι g) (target : ι) :
    finitePiLpScalarCommutator h
        (cmp99SourceGaugePrecision covariantLaplacian Qprime a) phi target =
      finitePiLpScalarCommutator h covariantLaplacian phi target +
        a • ∑ source : ι,
          (h target - h source) •
            (Qprime.adjoint.comp Qprime)
              (singleFinitePiLp source (phi source)) target := by
  rw [cmp99SourceGaugePrecision, finitePiLpScalarCommutator_add,
    finitePiLpScalarCommutator_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    PiLp.add_apply, PiLp.smul_apply,
    finitePiLpScalarCommutator_apply_eq_sum]

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Source-generated specialization of the third species.  The tower, its
adjoint mass and the normalization coefficient are all constructed inside
the literal physical precision. -/
theorem cmp99SourceGeneratedPhysicalPrecision_scalarCommutator_apply_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let OmegaFine :=
      cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    ∀ (h : ActiveGaugeRegion.Site OmegaFine → ℝ)
      (phi : ActiveGaugeZeroCochain OmegaFine (SUNLieCoord Nc))
      (target : ActiveGaugeRegion.Site OmegaFine),
      finitePiLpScalarCommutator h
          (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing
            epsilon background budget fineSmall) phi target =
        finitePiLpScalarCommutator h
            (cmp99ActiveRegionSourceCovariantLaplacian OmegaFine
              (matrixSUNAdjointModel Nc) background spacing) phi target +
          cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon •
            ∑ source : ActiveGaugeRegion.Site OmegaFine,
              (h target - h source) •
                (T.Qprime.adjoint.comp T.Qprime)
                  (singleFinitePiLp source (phi source)) target := by
  dsimp only
  intro h phi target
  exact finitePiLpScalarCommutator_sourceGaugePrecision_apply_eq h
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc) background spacing)
    ((cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)).
      weightedQprimeTower hd hM (matrixSUNAdjointModel Nc) spacing epsilon
        background budget.toRadiusChain fineSmall).Qprime
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)
    phi target

end

end YangMills.RG
