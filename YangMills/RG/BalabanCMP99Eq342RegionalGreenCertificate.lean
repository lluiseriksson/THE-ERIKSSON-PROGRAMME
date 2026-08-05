/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay

/-!
# CMP99 (3.42): the four local regional-Green estimates

PRE-VALIDATION: this source is present in the branch, its `.olean` has not
yet been materialized, and the result has not yet been compiler-verified.

CMP99 Theorem 3.1, equation (3.42), printed p. 397, bounds four actions of
one and the same localized Green: `G'`, `D G'`, `G' D*`, and `Delta G'`.
They share the constants `B0` and `delta0` and carry the scale vector
`[ell^2, ell, ell, 1]`.

This certificate fixes the operator definitionally to the canonical inverse
of the compressed regional precision.  It does not accept an independently
chosen Green family or identify the source estimate with the existing
`2 / coercivity` Combes--Thomas bound.  The latter would reintroduce the
Poincare wall ruled out by the sealed depth-zero no-go.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The source-visible scale vector in CMP99 (3.42). -/
def cmp99Eq342ScaleVector (ell : ℝ) : Fin 4 → ℝ
  | 0 => ell ^ 2
  | 1 => ell
  | 2 => ell
  | 3 => 1

/-- Source certificate for the four estimates in CMP99 (3.42).

All fields concern the literal canonical regional Green formed from `K` and
the same regional covariant differential.  In particular, the certificate
cannot be inhabited by supplying a different operator with convenient
bounds. -/
structure CMP99Eq342RegionalGreenCertificate
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (K : PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc)
    (c : ℝ) (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (B0 delta0 ell : ℝ) : Prop where
  B0_nonneg : 0 ≤ B0
  delta0_pos : 0 < delta0
  ell_pos : 0 < ell
  value_bound :
    FinitePiLpTypedExponentialKernelBound
      (cmp99RegionalDirichletGreen Omega K hc hKcoer)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (B0 * ell ^ 2) delta0
  left_derivative_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega K hc hKcoer))
      (fun target : PhysicalBond d N =>
        fun source : ActiveGaugeRegion.Site Omega =>
          finBoxDist target.1 source.1)
      (B0 * ell) delta0
  right_adjoint_derivative_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99RegionalDirichletGreen Omega K hc hKcoer).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint)
      (fun target : ActiveGaugeRegion.Site Omega =>
        fun source : PhysicalBond d N =>
          finBoxDist target.1 source.1)
      (B0 * ell) delta0
  laplacian_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega K hc hKcoer))
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      B0 delta0

/-- CMP96 (2.43) uses precisely the value and left-derivative components of
the stronger four-component CMP99 (3.42) package. -/
theorem CMP99Eq342RegionalGreenCertificate.cmp96Eq243_value_and_derivative
    {Omega : ActiveGaugeRegion d N}
    {rho : SUNAdjointModel Nc}
    {U : PhysicalGaugeBackground d N Nc}
    {spacing : ℝ}
    {K : PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc}
    {c : ℝ} {hc : 0 < c} {hKcoer : IsCoerciveCLM K c}
    {B0 delta0 ell : ℝ}
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing K c hc
      hKcoer B0 delta0 ell) :
    FinitePiLpTypedExponentialKernelBound
        (cmp99RegionalDirichletGreen Omega K hc hKcoer)
        (fun target source : ActiveGaugeRegion.Site Omega =>
          finBoxDist target.1 source.1)
        (B0 * ell ^ 2) delta0 ∧
      FinitePiLpTypedExponentialKernelBound
        ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
          (cmp99RegionalDirichletGreen Omega K hc hKcoer))
        (fun target : PhysicalBond d N =>
          fun source : ActiveGaugeRegion.Site Omega =>
            finBoxDist target.1 source.1)
        (B0 * ell) delta0 :=
  ⟨C.value_bound, C.left_derivative_bound⟩

end

end YangMills.RG
