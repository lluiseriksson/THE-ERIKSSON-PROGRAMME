/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision
import YangMills.RG.BlockLattice
import YangMills.RG.FinitePiLpTypedKernel

/-!
# CMP99 (3.42): the four local regional-Green estimates

PRE-VALIDATION: this source is present in the branch, its `.olean` has not
yet been materialized, and the result has not yet been compiler-verified.

CMP99 Theorem 3.1, equation (3.42), printed p. 397, bounds four actions of
one and the same localized Green: `G'`, `D G'`, `G' D*`, and `Delta G'`.
They share the constants `B0` and `delta0` and carry the scale vector
`[ell^2, ell, ell, 1]`.  Its decay distance is the source block-scale
distance, realized here by first applying the literal `blockSite` map.  It is
not the stronger raw fine-site distance.

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

variable {m q Nc : ℕ} [NeZero m] [NeZero q] [NeZero Nc]

/-- The source-visible scale vector in CMP99 (3.42). -/
def cmp99Eq342ScaleVector (ell : ℝ) : Fin 4 → ℝ
  | 0 => ell ^ 2
  | 1 => ell
  | 2 => ell
  | 3 => 1

/-- The block-scale distance printed in CMP99 (3.42).

The map is fixed definitionally to the physical block map.  In particular,
this is neither the raw fine-site distance nor an arbitrary distance supplied
by a caller. -/
def cmp99Eq342RescaledBlockDist
    (m q : ℕ) [NeZero m]
    (x y : FinBox 4 (m * (2 * q))) : ℕ :=
  finBoxDist (blockSite m (2 * q) x) (blockSite m (2 * q) y)

/-- Source certificate for the four estimates in CMP99 (3.42).

All fields concern the literal canonical regional Green formed from `K` and
the same regional covariant differential.  In particular, the certificate
cannot be inhabited by supplying a different operator with convenient
bounds. -/
structure CMP99Eq342RegionalGreenCertificate
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    (spacing : ℝ)
    (K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (B0 delta0 ell : ℝ) : Prop where
  B0_pos : 0 < B0
  carrier_nonempty : Nonempty (ActiveGaugeRegion.Site Omega)
  delta0_pos : 0 < delta0
  ell_pos : 0 < ell
  value_bound :
    FinitePiLpTypedExponentialKernelBound
      (cmp99RegionalDirichletGreen Omega K hc hKcoer)
      (fun target source : ActiveGaugeRegion.Site Omega =>
        cmp99Eq342RescaledBlockDist m q target.1 source.1)
      (B0 * ell ^ 2) delta0
  left_derivative_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega K hc hKcoer))
      (fun target : PhysicalBond 4 (m * (2 * q)) =>
        fun source : ActiveGaugeRegion.Site Omega =>
          cmp99Eq342RescaledBlockDist m q target.1 source.1)
      (B0 * ell) delta0
  right_adjoint_derivative_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99RegionalDirichletGreen Omega K hc hKcoer).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint)
      (fun target : ActiveGaugeRegion.Site Omega =>
        fun source : PhysicalBond 4 (m * (2 * q)) =>
          cmp99Eq342RescaledBlockDist m q target.1 source.1)
      (B0 * ell) delta0
  laplacian_bound :
    FinitePiLpTypedExponentialKernelBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega K hc hKcoer))
      (fun target source : ActiveGaugeRegion.Site Omega =>
        cmp99Eq342RescaledBlockDist m q target.1 source.1)
      B0 delta0

/-- Strict source positivity rules out the zero-amplitude witness while still
providing the nonnegativity needed by downstream norm estimates. -/
theorem CMP99Eq342RegionalGreenCertificate.B0_nonneg
    {Omega : ActiveGaugeRegion 4 (m * (2 * q))}
    {rho : SUNAdjointModel Nc}
    {U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc}
    {spacing : ℝ}
    {K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc)}
    {c : ℝ} {hc : 0 < c} {hKcoer : IsCoerciveCLM K c}
    {B0 delta0 ell : ℝ}
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing K c hc
      hKcoer B0 delta0 ell) :
    0 ≤ B0 :=
  C.B0_pos.le

/-- CMP96 (2.43) uses precisely the value and left-derivative components of
the stronger four-component CMP99 (3.42) package. -/
theorem CMP99Eq342RegionalGreenCertificate.cmp96Eq243_value_and_derivative
    {Omega : ActiveGaugeRegion 4 (m * (2 * q))}
    {rho : SUNAdjointModel Nc}
    {U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc}
    {spacing : ℝ}
    {K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc)}
    {c : ℝ} {hc : 0 < c} {hKcoer : IsCoerciveCLM K c}
    {B0 delta0 ell : ℝ}
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U spacing K c hc
      hKcoer B0 delta0 ell) :
    FinitePiLpTypedExponentialKernelBound
        (cmp99RegionalDirichletGreen Omega K hc hKcoer)
        (fun target source : ActiveGaugeRegion.Site Omega =>
          cmp99Eq342RescaledBlockDist m q target.1 source.1)
        (B0 * ell ^ 2) delta0 ∧
      FinitePiLpTypedExponentialKernelBound
        ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
          (cmp99RegionalDirichletGreen Omega K hc hKcoer))
        (fun target : PhysicalBond 4 (m * (2 * q)) =>
          fun source : ActiveGaugeRegion.Site Omega =>
            cmp99Eq342RescaledBlockDist m q target.1 source.1)
        (B0 * ell) delta0 :=
  ⟨C.value_bound, C.left_derivative_bound⟩

end

end YangMills.RG
