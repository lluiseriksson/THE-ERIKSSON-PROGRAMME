/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99LocalizedParametrix
import YangMills.RG.BalabanCMP99SectionCPointedFactorDictionary
import YangMills.RG.PhysicalResolventCorrection

/-!
# A first literal nonzero CMP99 Section-C factor species

CMP99 Section C explicitly lists factors containing covariance differences
`C_{Pi0} - C_Pi`, while leaving the complete factor alphabet open with
"etc.".  This file formalizes precisely that printed difference for the
physical localized covariances already constructed in the repository.

The result is intentionally a partial source dictionary.  We do not identify
the primed propagator `G'` with `C`, do not assign a closed `alpha` label to
the difference, and do not manufacture the source-ambiguous operator
`K(h'_Pi)`.  What is closed here is the literal covariance subtraction and
its exact second-resolvent factorization.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The printed unprimed Section-C covariance-difference species
`C_{S0} - C_{S1}`.  The two physical supports remain explicit because CMP99
does not provide a unique domain-to-support assignment for the examples. -/
noncomputable def cmp99SectionCCovarianceDifference
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) : PhysicalEndomorphism d N Nc :=
  cmp99LocalizedPhysicalCovariance K S0 hc hmass hK -
    cmp99LocalizedPhysicalCovariance K S1 hc hmass hK

@[simp] theorem cmp99SectionCCovarianceDifference_apply
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (x : PhysicalGaugeOneCochain d N Nc) :
    cmp99SectionCCovarianceDifference K S0 S1 hc hmass hK x =
      cmp99LocalizedPhysicalCovariance K S0 hc hmass hK x -
        cmp99LocalizedPhysicalCovariance K S1 hc hmass hK x :=
  rfl

/-- Exact projection-level formula for the precision difference appearing in
the resolvent identity. -/
theorem cmp99LocalizedPhysicalPrecision_sub_eq_projectionFormula
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : Finset (PhysicalBond d N)) (mass : ℝ) :
    cmp99LocalizedPhysicalPrecision K S1 mass -
        cmp99LocalizedPhysicalPrecision K S0 mass =
      (physicalBondProjection S1).comp
          (K.comp (physicalBondProjection S1)) -
        (physicalBondProjection S0).comp
          (K.comp (physicalBondProjection S0)) +
        mass • (physicalBondProjection S0 - physicalBondProjection S1) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp99LocalizedPhysicalPrecision,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    physicalBondComplementProjection,
    ContinuousLinearMap.id_apply]
  module

/-- Source-facing second resolvent identity for the printed difference.  All
inverse hypotheses are generated internally from localized coercivity. -/
theorem cmp99SectionCCovarianceDifference_eq_resolventProduct
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    cmp99SectionCCovarianceDifference K S0 S1 hc hmass hK =
      (cmp99LocalizedPhysicalCovariance K S0 hc hmass hK).comp
        ((cmp99LocalizedPhysicalPrecision K S1 mass -
          cmp99LocalizedPhysicalPrecision K S0 mass).comp
            (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK)) := by
  unfold cmp99SectionCCovarianceDifference
  exact covariance_sub_eq_comp_precision_sub_comp
    (cmp99LocalizedPhysicalPrecision K S1 mass)
    (cmp99LocalizedPhysicalPrecision K S0 mass)
    (cmp99LocalizedPhysicalCovariance K S1 hc hmass hK)
    (cmp99LocalizedPhysicalCovariance K S0 hc hmass hK)
    (cmp99LocalizedPhysicalCovariance_comp_precision K S0 hc hmass hK)
    (cmp99LocalizedPhysicalPrecision_comp_covariance K S1 hc hmass hK)

/-- The Section-C covariance difference vanishes when its two source supports
coincide.  This is an exact dictionary check, not a decay estimate. -/
@[simp] theorem cmp99SectionCCovarianceDifference_self
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    cmp99SectionCCovarianceDifference K S S hc hmass hK = 0 := by
  simp [cmp99SectionCCovarianceDifference]

end

end YangMills.RG
