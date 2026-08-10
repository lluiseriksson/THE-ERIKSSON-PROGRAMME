/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCovariantLaplacianCutoffIdentity

/-!
# PRE-VALIDATION: flat periodic CMP99 ambient Laplacian

Source is present, the corresponding `.olean` has not yet been materialized,
and the result has not yet been compiler-verified.

CMP89 (2.43)--(2.48) diagonalizes the zero-background periodic precision.
Before introducing Fourier modes, this module proves the exact first
dictionary entry: the literal CMP99 ambient covariant Laplacian at the
trivial gauge background is the ordinary symmetric nearest-neighbour
periodic stencil, with the complete `spacing⁻²` normalization visible.

No Fourier transform, eigenvalue formula, average symbol, Green inverse or
regional transport is asserted here. Those remain separate downstream
obligations.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal trivial physical gauge background. Giving the unit field a
source-level name fixes its group-valued type before any specialization. -/
def cmp99FlatGaugeBackground (d N Nc : ℕ)
    [NeZero d] [NeZero N] [NeZero Nc] :
    PhysicalGaugeBackground d N Nc :=
  fun _ => 1

/-- Ordinary symmetric nearest-neighbour stencil on the periodic fine
lattice. This is the zero-background differential part of the CMP99
precision before the physical `spacing⁻²` factor is applied. -/
def cmp99FlatPeriodicLaplacianStencil
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    SUNLieCoord Nc :=
  ∑ i : Fin d,
    ((phi x - phi (x.shift i)) - (phi (x.shiftBack i) - phi x))

/-- At the trivial gauge background every adjoint transport is the identity,
so the literal covariant stencil reduces exactly to the flat periodic
nearest-neighbour stencil. -/
theorem cmp99AmbientCovariantLaplacianStencil_one
    (rho : SUNAdjointModel Nc) (phi : PhysicalGaugeZeroCochain d N Nc)
    (x : FinBox d N) :
    cmp99AmbientCovariantLaplacianStencil rho
        (cmp99FlatGaugeBackground d N Nc) phi x =
      cmp99FlatPeriodicLaplacianStencil phi x := by
  simp [cmp99AmbientCovariantLaplacianStencil,
    cmp99FlatPeriodicLaplacianStencil, rho.ad_one_apply]

/-- Exact periodic zero-background specialization of the generated ambient
scaled Laplacian. The source normalization is `spacing⁻¹ • spacing⁻¹`, with
no hidden convention or nonzero-spacing premise. -/
theorem cmp99GeneratedAmbientScaledCovariantLaplacian_one_apply
    (rho : SUNAdjointModel Nc) (spacing : ℝ)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho
        (cmp99FlatGaugeBackground d N Nc) spacing phi x =
      spacing⁻¹ • spacing⁻¹ • cmp99FlatPeriodicLaplacianStencil phi x := by
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_stencil,
    cmp99AmbientCovariantLaplacianStencil_one]

end

end YangMills.RG
