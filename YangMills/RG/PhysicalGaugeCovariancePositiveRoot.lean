/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FiniteDimensionalRealPositiveSqrt
import YangMills.RG.PhysicalGaugeCovarianceLocalization

/-!
# Canonical positive root for a localized physical covariance

This module discharges the algebraic square-root fields of
`PhysicalLocalizedCovarianceRootCertificate` whenever the supplied physical
covariance is positive.  The root is the canonical finite-dimensional real
spectral root, and its norm bound is recorded exactly as its operator norm.

Consequently, after a localized covariance certificate and positivity are
available, only the genuinely analytic root-kernel bound remains as an input.
No spatial decay theorem is manufactured here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- Assemble the physical localized covariance-root certificate using the
canonical finite-dimensional positive root.

The remaining source input `hrootKernel` is precisely the spatial localization
statement for that root.  The norm bound is exact but non-quantitative. -/
theorem physicalLocalizedCovarianceRootCertificate_of_positive_covariance
    {d N Nc : ℕ} [NeZero N]
    {precision covariance :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    (hcov :
      PhysicalLocalizedCovarianceCertificate
        precision covariance covNormBound covWeight)
    (hcovPositive : covariance.IsPositive)
    (hrootKernel :
      PhysicalCovarianceKernelBound
        (finiteDimensionalRealPositiveSqrt covariance hcovPositive)
        rootWeight) :
    PhysicalLocalizedCovarianceRootCertificate
      precision covariance
      (finiteDimensionalRealPositiveSqrt covariance hcovPositive)
      covNormBound
      ‖finiteDimensionalRealPositiveSqrt covariance hcovPositive‖
      covWeight rootWeight := by
  apply physicalLocalizedCovarianceRootCertificate_of_source hcov
  · exact finiteDimensionalRealPositiveSqrt_comp_self covariance hcovPositive
  · exact le_rfl
  · intro x y
    exact
      (finiteDimensionalRealPositiveSqrt_inner_left_eq_inner_right
        covariance hcovPositive x y).symm
  · intro y
    exact finiteDimensionalRealPositiveSqrt_inner_nonneg
      covariance hcovPositive y
  · exact hrootKernel

end


end YangMills.RG
