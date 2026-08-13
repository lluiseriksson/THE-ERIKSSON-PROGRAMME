/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalComplexZeroExtensionDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
# Source-pinned generated terminal complex field data

This package retains only the literal generated active real field.  Its real
Dirichlet extension and transported complex full-box field are definitions,
not caller-supplied choices.  The sealed global zero-extension dictionary and
the regional Laplacian compression theorem therefore concern the same field.

No equality of carriers, flat-background dictionary, periodic-stencil
transport, full precision, inverse or Green operator is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A generated active field with no independently chosen ambient field. -/
structure CMP99SourceGeneratedTerminalComplexFieldData
    (Omega : ActiveGaugeRegion d N) (depth : ℕ) where
  activeField : PiLp 2 (fun _ : ActiveGaugeRegion.Site
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
      SUNLieCoord Nc)

namespace CMP99SourceGeneratedTerminalComplexFieldData

/-- Canonical package of a literal generated active field. -/
def ofActiveField
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (eta : PiLp 2 (fun _ : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        SUNLieCoord Nc)) :
    CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth where
  activeField := eta

/-- Literal real Dirichlet extension of the retained active field. -/
noncomputable def realZeroExtension
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth) :
    PhysicalGaugeZeroCochain d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc :=
  extendZeroZeroCLM
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) D.activeField

/-- Literal transported complex full-box field determined by `activeField`. -/
noncomputable def complexZeroExtension
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth) :
    FinBox d ((M ^ (depth + 1)) * N) → SUNLieComplexCoord Nc :=
  cmp99SourceGeneratedTerminalComplexZeroExtension
    (M := M) (Nc := Nc) Omega depth D.activeField

omit [NeZero d] [NeZero Nc] in
/-- The two canonical extensions are related globally through the sealed
transported-delta dictionary. -/
theorem complexZeroExtension_apply_eq_complexification_realZeroExtension
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (x : FinBox d (cmp99RegionalLatticeSize M N (depth + 1))) :
    D.complexZeroExtension
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := d) M N (depth + 1) x) =
      cmp99SUNLieCoordComplexificationLM Nc (D.realZeroExtension x) := by
  simpa [complexZeroExtension, realZeroExtension] using
    cmp99SourceGeneratedTerminalComplexZeroExtension_apply_eq_complexification_extendZero
      (M := M) (Nc := Nc) Omega depth D.activeField x

/-- The regional source Laplacian is the Dirichlet compression of the ambient
operator acting on the same canonical real zero extension. -/
theorem activeLaplacian_apply_eq_compression
    {Omega : ActiveGaugeRegion d N} {depth : ℕ}
    (D : CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc) Omega depth)
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d
      (cmp99RegionalLatticeSize M N (depth + 1)) Nc)
    (spacing : ℝ) :
    cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        rho U spacing D.activeField =
      restrictZeroCLM
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
          D.realZeroExtension) := by
  simpa [realZeroExtension] using
    cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      rho U spacing D.activeField

end CMP99SourceGeneratedTerminalComplexFieldData

end

end YangMills.RG
