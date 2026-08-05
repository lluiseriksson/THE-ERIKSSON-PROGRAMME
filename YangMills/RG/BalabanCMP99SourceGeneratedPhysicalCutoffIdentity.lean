/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCovariantLaplacianCutoffIdentity
import YangMills.RG.BalabanCMP99SourceGeneratedQprimeMassCutoffIdentity
import YangMills.RG.BalabanCMP99SourceEq395HeadDictionary

/-!
# PRE-VALIDATION: the complete generated physical cutoff identity in CMP99 (3.88)

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

This file combines the three literal algebraic species in CMP99 (3.88): the
covariant link derivative, the scalar cutoff-Laplacian correction and the
normalized `Q'^* Q'` kernel sum.  Extension and restriction are kept visible
until the ambient product rule has been transported to the active region.
No finite-range collar, overlap estimate or contraction hypothesis is used in
the exact identity; those belong to the subsequent estimate of `norm R'`.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Restriction of the ambient link-derivative species to one active
Dirichlet carrier. -/
noncomputable def cmp99ActiveCovariantCutoffLinkDerivative
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (h : FinBox d N → ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  restrictZeroCLM Omega
    (cmp99CovariantCutoffLinkDerivative rho U spacing h
      (extendZeroZeroCLM Omega phi))

/-- Restriction of the ambient scalar cutoff-Laplacian species to one active
Dirichlet carrier. -/
noncomputable def cmp99ActiveCutoffLaplacianCorrection
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ)
    (h : FinBox d N → ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  restrictZeroCLM Omega
    (cmp99CutoffLaplacianCorrection spacing h
      (extendZeroZeroCLM Omega phi))

/-- The ambient two-species product rule descends exactly to an arbitrary
active region.  The multiplier intertwiners need no support hypothesis. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_scalarMultiplier_apply
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (h : FinBox d N → ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site Omega) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing
        (finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
          (fun x : ActiveGaugeRegion.Site Omega => h x.1) phi) target =
      h target.1 •
          cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing phi target -
        cmp99ActiveCovariantCutoffLinkDerivative Omega rho U spacing h phi target +
        cmp99ActiveCutoffLaplacianCorrection Omega spacing h phi target := by
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let Hambient := finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h
  let Hlocal := finitePiLpScalarMultiplier (g := SUNLieCoord Nc)
    (fun x : ActiveGaugeRegion.Site Omega => h x.1)
  have hHE : Hambient.comp E = E.comp Hlocal := by
    exact finitePiLpScalarMultiplier_comp_extendZeroZeroCLM Omega h
  have hHEphi : Hambient (E phi) = E (Hlocal phi) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun A => A phi) hHE
  rw [cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression,
    cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  change
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
        (E (Hlocal phi)) target.1 =
      h target.1 •
          cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
            (E phi) target.1 -
        cmp99CovariantCutoffLinkDerivative rho U spacing h
          (E phi) target.1 +
        cmp99CutoffLaplacianCorrection spacing h (E phi) target.1
  rw [← hHEphi]
  exact cmp99GeneratedAmbientScaledCovariantLaplacian_scalarMultiplier
    rho U spacing h (E phi) target.1

/-- Active-region first-two-species formula in the commutator orientation
`h Delta_U - Delta_U h` used by `K(h)` in CMP99 (3.88). -/
theorem finitePiLpScalarCommutator_activeCovariantLaplacian_apply_eq
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (h : FinBox d N → ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site Omega) :
    finitePiLpScalarCommutator
        (fun x : ActiveGaugeRegion.Site Omega => h x.1)
        (cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing)
        phi target =
      cmp99ActiveCovariantCutoffLinkDerivative Omega rho U spacing h phi target -
        cmp99ActiveCutoffLaplacianCorrection Omega spacing h phi target := by
  rw [finitePiLpScalarCommutator]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    finitePiLpScalarMultiplier_apply]
  rw [cmp99ActiveRegionSourceCovariantLaplacian_scalarMultiplier_apply]
  module

/-- Exact three-species split for an active source precision whose
Laplacian is the literal covariant one.  The two differential species and
the normalized mass kernel sum remain separately visible. -/
theorem finitePiLpScalarCommutator_activeSourceGaugePrecision_apply_eq
    {κ : Type*} [Fintype κ]
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (h : FinBox d N → ℝ)
    (Qprime : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      FinitePiLpField κ (SUNLieCoord Nc))
    (a : ℝ) (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site Omega) :
    finitePiLpScalarCommutator
        (fun x : ActiveGaugeRegion.Site Omega => h x.1)
        (cmp99SourceGaugePrecision
          (cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing)
          Qprime a) phi target =
      cmp99ActiveCovariantCutoffLinkDerivative Omega rho U spacing h phi target -
        cmp99ActiveCutoffLaplacianCorrection Omega spacing h phi target +
        a • ∑ source : ActiveGaugeRegion.Site Omega,
          (h target.1 - h source.1) •
            (Qprime.adjoint.comp Qprime)
              (singleFinitePiLp source (phi source)) target := by
  rw [finitePiLpScalarCommutator_sourceGaugePrecision_apply_eq,
    finitePiLpScalarCommutator_activeCovariantLaplacian_apply_eq]

/-- Literal generated-precision specialization of all three species in
CMP99 (3.88).  The tower `Q'`, its adjoint mass and its scalar coefficient
are constructed internally from the source data. -/
theorem cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_apply_eq
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (h : FinBox d (cmp99RegionalLatticeSize M N (depth + 1)) → ℝ)
    (phi : ActiveGaugeZeroCochain
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (SUNLieCoord Nc))
    (target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))) :
    let OmegaFine := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    let mass := cmp99SourceGeneratedPhysicalMass
      d M (depth + 1) spacing epsilon
    finitePiLpScalarCommutator
        (fun x : ActiveGaugeRegion.Site OmegaFine => h x.1)
        (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
          background budget fineSmall) phi target =
      cmp99ActiveCovariantCutoffLinkDerivative OmegaFine
          (matrixSUNAdjointModel Nc) background spacing h phi target -
        cmp99ActiveCutoffLaplacianCorrection OmegaFine spacing h phi target +
        mass • ∑ source : ActiveGaugeRegion.Site OmegaFine,
          (h target.1 - h source.1) •
            (T.Qprime.adjoint.comp T.Qprime)
              (singleFinitePiLp source (phi source)) target := by
  dsimp only
  rw [cmp99SourceGeneratedPhysicalPrecision_eq_sourceGaugePrecision]
  exact finitePiLpScalarCommutator_activeSourceGaugePrecision_apply_eq
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing h
    ((cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)).weightedQprimeTower hd hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall).Qprime
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)
    phi target

end

end YangMills.RG
