/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# PRE-VALIDATION: the two differential terms in CMP99 (3.88)

The source of this module is present, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP99 (3.88), printed p. 409, expands the covariant-Laplacian part of
`Delta'_a (h lambda)` into a link-derivative term and a scalar cutoff-
Laplacian term.  This file derives that identity from the literal periodic
covariant stencil.  It does not postulate either correction as an arbitrary
operator.

The two orientations incident to `x` are kept explicit.  This matters for the
sign convention: `covariantD0CLM` is the negative of the derivative printed in
CMP99, while each scalar cutoff difference changes sign at the same time.
Their product therefore has the printed orientation.

This module covers only the first two correction species in (3.88).  The
normalized `Q'^* Q'` term and the complete physical three-term identity remain
open.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Pure module algebra for one positive direction and its incident reverse
direction.  It is isolated from the lattice so elaboration failures here can
be reproduced against Mathlib alone. -/
theorem cmp99_covariant_cutoff_product_rule_direction
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h₀ hplus hminus : ℝ) (v avplus avminus : E) :
    (h₀ • v - hplus • avplus) - (hminus • avminus - h₀ • v) =
      h₀ • ((v - avplus) - (avminus - v)) -
        ((h₀ - hplus) • (v - avplus) +
          (h₀ - hminus) • (v - avminus)) +
        ((h₀ - hplus) + (h₀ - hminus)) • v := by
  module

/-- The unscaled nearest-neighbour stencil underlying
`cmp99GeneratedAmbientScaledCovariantLaplacian`. -/
def cmp99AmbientCovariantLaplacianStencil
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    SUNLieCoord Nc :=
  ∑ i : Fin d,
    ((phi x -
        rho.adCLM (U (ConcreteEdge.mk x i true)) (phi (x.shift i))) -
      (rho.adCLM
          (U (positiveEdgeOfPhysicalBond
            ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
          (phi (x.shiftBack i)) - phi x))

/-- The generated ambient Laplacian is exactly `spacing^-2` times its
unscaled stencil.  No positivity or nonzero-spacing premise is needed for this
algebraic identity. -/
theorem cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_stencil
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (phi : PhysicalGaugeZeroCochain d N Nc)
    (x : FinBox d N) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing phi x =
      spacing⁻¹ • spacing⁻¹ •
        cmp99AmbientCovariantLaplacianStencil rho U phi x := by
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply]
  simp only [PiLp.smul_apply, covariantD0CLM_apply, map_smul, map_sub,
    positiveEdgeOfPhysicalBond, rho.ad_inv_apply_ad,
    FinBox.shift_shiftBack]
  simp only [cmp99AmbientCovariantLaplacianStencil,
    positiveEdgeOfPhysicalBond, Finset.smul_sum, smul_sub]

/-- The source-facing link-derivative correction in the first line of CMP99
(3.88).  Both bonds in the star of `x` are written using the positive-bond
carrier; the reverse bond is parallel transported back to `x`. -/
def cmp99CovariantCutoffLinkDerivative
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (h : FinBox d N → ℝ)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    SUNLieCoord Nc :=
  spacing⁻¹ • spacing⁻¹ •
    ∑ i : Fin d,
      ((h x - h (x.shift i)) •
          (phi x -
            rho.adCLM (U (ConcreteEdge.mk x i true)) (phi (x.shift i))) +
        (h x - h (x.shiftBack i)) •
          (phi x -
            rho.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
              (phi (x.shiftBack i))))

/-- The source-facing scalar cutoff-Laplacian correction in CMP99 (3.88),
with the positive `D^*D` convention used by the physical precision. -/
def cmp99CutoffLaplacianCorrection
    (spacing : ℝ) (h : FinBox d N → ℝ)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    SUNLieCoord Nc :=
  spacing⁻¹ • spacing⁻¹ •
    ∑ i : Fin d,
      ((h x - h (x.shift i)) + (h x - h (x.shiftBack i))) • phi x

/-- Exact unscaled product rule for the covariant stencil. -/
theorem cmp99AmbientCovariantLaplacianStencil_scalarMultiplier
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (h : FinBox d N → ℝ) (phi : PhysicalGaugeZeroCochain d N Nc)
    (x : FinBox d N) :
    cmp99AmbientCovariantLaplacianStencil rho U
        (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h phi) x =
      h x • cmp99AmbientCovariantLaplacianStencil rho U phi x -
        (∑ i : Fin d,
          ((h x - h (x.shift i)) •
              (phi x -
                rho.adCLM (U (ConcreteEdge.mk x i true))
                  (phi (x.shift i))) +
            (h x - h (x.shiftBack i)) •
              (phi x -
                rho.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
                  (phi (x.shiftBack i))))) +
        ∑ i : Fin d,
          ((h x - h (x.shift i)) + (h x - h (x.shiftBack i))) • phi x := by
  simp only [cmp99AmbientCovariantLaplacianStencil,
    finitePiLpScalarMultiplier_apply, map_smul]
  conv_rhs =>
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact cmp99_covariant_cutoff_product_rule_direction
    (h x) (h (x.shift i)) (h (x.shiftBack i))
    (phi x)
    (rho.adCLM (U (ConcreteEdge.mk x i true)) (phi (x.shift i)))
    (rho.adCLM
      (U (positiveEdgeOfPhysicalBond
        ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
      (phi (x.shiftBack i)))

/-- Literal first-two-species specialization of CMP99 (3.88):

`Delta_U(h phi) = h Delta_U(phi) - linkDerivative + cutoffLaplacian`.

The statement uses the same multiplier as the regional Green construction
and the literal generated ambient covariant Laplacian. -/
theorem cmp99GeneratedAmbientScaledCovariantLaplacian_scalarMultiplier
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (h : FinBox d N → ℝ)
    (phi : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d N) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
        (finitePiLpScalarMultiplier (g := SUNLieCoord Nc) h phi) x =
      h x • cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing phi x -
        cmp99CovariantCutoffLinkDerivative rho U spacing h phi x +
        cmp99CutoffLaplacianCorrection spacing h phi x := by
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_stencil,
    cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_stencil,
    cmp99AmbientCovariantLaplacianStencil_scalarMultiplier]
  simp only [cmp99CovariantCutoffLinkDerivative,
    cmp99CutoffLaplacianCorrection]
  module

end

end YangMills.RG
