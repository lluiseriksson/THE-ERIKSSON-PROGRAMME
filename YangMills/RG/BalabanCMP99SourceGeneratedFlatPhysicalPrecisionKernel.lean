/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Direct kernel of the generated physical precision at the flat background

The generated physical precision uses the bundled terminal Hilbert space of
the source tower, whereas the sealed flat recursion exposes its dependent
terminal coordinate type.  Transport between those equal Hilbert bundles is
isometric and therefore leaves `Q'^* Q'` unchanged.  This file proves that
fact and uses it to specialize the literal physical precision to the flat
background.

The endpoint keeps the covariant Laplacian and the generated mass as two
separate literal summands.  Its mass kernel uses the coordinatewise generated
terminal owner and retains both the printed physical mass coefficient and the
counting-adjoint normalization `(M^{-d})^(2 * (depth + 1))`.

This is a flat physical-operator dictionary.  It does not identify CMP99
strata, match an interacting precision, construct an inverse, prove a regional
Green bound or attain window 15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Transporting only the codomain of a Hilbert-space map leaves its adjoint
square unchanged on the source space. -/
theorem cmp99SourceTerminalCLMTransport_adjoint_comp_self
    {E F F' : CMP99SourceWeightedTowerHilbertSpace}
    (hF : F = F') (Q : E.carrier →L[ℝ] F.carrier) :
    (cmp99SourceTerminalCLMTransport rfl hF Q).adjoint.comp
        (cmp99SourceTerminalCLMTransport rfl hF Q) =
      Q.adjoint.comp Q := by
  rw [← cmp99SourceTerminalCLMTransport_adjoint,
    cmp99SourceTerminalCLMTransport_comp]
  rfl

/-- Literal generated physical precision specialized to the flat background
and the internally constructed zero-radius source budget. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing : ℝ) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing 0
    (cmp99SourceFlatGaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
    (cmp99SourceFlatZeroClosedBudget (d := d) (M := M) (Nc := Nc)
      (depth + 1))
    cmp99SourceFlatGaugeConfig_zero_small

/-- The same flat precision written with the sealed explicit generated
`Q'` recursion.  Naming this operator keeps the public comparison theorem
from elaborating the full dependent terminal tower in its result type. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) (spacing : ℝ) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc)
      (cmp99SourceFlatGaugeConfig d
        (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
      spacing)
    regions.flatExplicitQprime
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing 0)

/-- Exact flat specialization of the physical precision: the covariant
Laplacian is unchanged and the generated mass is rewritten to the explicit
flat `Q'` recursion. -/
theorem cmp99SourceGeneratedFlatPhysicalPrecision_eq_explicit
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing : ℝ) :
    cmp99SourceGeneratedFlatPhysicalPrecision hd hM Omega depth spacing =
      cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
        (d := d) (M := M) (N := N) (Nc := Nc) Omega depth spacing := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let background := cmp99SourceFlatGaugeConfig d
    (cmp99RegionalLatticeSize M N (depth + 1)) Nc
  let chain := cmp99SourceFlatZeroRadiusChain
    (d := d) (M := M) (Nc := Nc) (depth + 1)
  let fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 :=
    cmp99SourceFlatGaugeConfig_zero_small
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing 0
    background chain fineSmall
  let hT : T.TerminalSpace = regions.terminalHilbertSpace Nc :=
    regions.weightedQprimeTower_terminalSpace_eq hd hM
      (matrixSUNAdjointModel Nc) spacing 0 background chain fineSmall
  let hCoord : regions.terminalHilbertSpace Nc =
      regions.terminalCoordinateHilbertSpace (Nc := Nc) :=
    regions.terminalHilbertSpace_eq_coordinate
  have htransported :
      (regions.transportedQprime hd hM (matrixSUNAdjointModel Nc) spacing 0
          background chain fineSmall).adjoint.comp
          (regions.transportedQprime hd hM (matrixSUNAdjointModel Nc) spacing 0
            background chain fineSmall) =
        T.Qprime.adjoint.comp T.Qprime := by
    change
      (cmp99SourceTerminalCLMTransport rfl (hT.trans hCoord)
          T.Qprime).adjoint.comp
          (cmp99SourceTerminalCLMTransport rfl (hT.trans hCoord)
            T.Qprime) =
        T.Qprime.adjoint.comp T.Qprime
    exact cmp99SourceTerminalCLMTransport_adjoint_comp_self
      (hT.trans hCoord) T.Qprime
  have hphysical := regions.physicalQprime_eq_transported hd hM
    (matrixSUNAdjointModel Nc) spacing 0 background chain fineSmall
  have hflat := regions.flatPhysicalQprime_eq_explicit hd hM
    (matrixSUNAdjointModel Nc) spacing
  have hQ :
      regions.transportedQprime hd hM (matrixSUNAdjointModel Nc) spacing 0
          background chain fineSmall = regions.flatExplicitQprime := by
    calc
      _ = regions.physicalQprime hd hM (matrixSUNAdjointModel Nc) spacing 0
          background chain fineSmall := hphysical.symm
      _ = regions.flatPhysicalQprime hd hM (matrixSUNAdjointModel Nc)
          spacing := rfl
      _ = regions.flatExplicitQprime := hflat
  have hmass : T.Qprime.adjoint.comp T.Qprime =
      regions.flatExplicitQprime.adjoint.comp regions.flatExplicitQprime :=
    htransported.symm.trans (congrArg (fun Q => Q.adjoint.comp Q) hQ)
  change cmp99SourceGaugePrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (matrixSUNAdjointModel Nc)
        (cmp99SourceFlatGaugeConfig d
          (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
        spacing)
      T.Qprime
      (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing 0) =
    cmp99SourceGaugePrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (matrixSUNAdjointModel Nc)
        (cmp99SourceFlatGaugeConfig d
          (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
        spacing)
      regions.flatExplicitQprime
      (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing 0)
  unfold cmp99SourceGaugePrecision
  rw [hmass]

/-- Coordinate-probe kernel of the literal flat generated physical precision.
The Laplacian and generated mass remain separate, and the mass term uses the
direct coordinatewise order-`M^(depth+1)` owner. -/
theorem cmp99SourceGeneratedFlatPhysicalPrecision_single_apply
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing : ℝ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
    (v : SUNLieCoord Nc) :
    cmp99SourceGeneratedFlatPhysicalPrecision hd hM Omega depth spacing
        (singleFinitePiLp source v) target =
      cmp99ActiveRegionSourceCovariantLaplacian
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
          (matrixSUNAdjointModel Nc)
          (cmp99SourceFlatGaugeConfig d
            (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
          spacing (singleFinitePiLp source v) target +
        cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing 0 •
          (if cmp99GeneratedTerminalBlockSite M N (depth + 1) target.1 =
              cmp99GeneratedTerminalBlockSite M N (depth + 1) source.1 then
            (cmp99SourceBlockAverageWeight M d) ^ (2 * (depth + 1)) • v
          else 0) := by
  rw [cmp99SourceGeneratedFlatPhysicalPrecision_eq_explicit]
  unfold cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
  unfold cmp99SourceGaugePrecision
  rw [ContinuousLinearMap.add_apply, PiLp.add_apply,
    ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply]

end

end YangMills.RG
