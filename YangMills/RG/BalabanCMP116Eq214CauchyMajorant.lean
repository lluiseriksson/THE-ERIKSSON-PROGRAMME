/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214AnalyticResummation
import YangMills.RG.BalabanCMP116Eq214CauchyEstimate

/-!
# CMP116 equation (2.26): canonical Cauchy majorants

This module removes the arbitrary `termWeight` from the analytic resummation.
Given a real boundary majorant for the integrand, the term weight is fixed to
the inverse-radius loss proved for the two nested Cauchy families.

Consequently the generic Lemma-3 finite-sum theorem can be invoked from two
source-facing obligations only:

1. the physical integrand obeys its declared contour bound;
2. the resulting explicit weights satisfy the remaining geometric budget.

The second obligation is the still-open resummation content of (2.16)--(2.26);
it is not stored in a record or assumed as a pointwise activity estimate.
-/

namespace YangMills.RG

/-- Explicit inverse-radius weight associated with one literal (2.14) term. -/
noncomputable def cmp116Eq214CauchyTermWeight
    {nDelta nY : ℕ} {Bond X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Ψ Φ E)
    (boundaryMajorant : ℝ) : ℝ :=
  cmp116Eq214CauchyRate nDelta A.deltaRadius
    (cmp116Eq214CauchyRate nY A.yRadius boundaryMajorant)

/-- Physical analytic resummation with both the complex summand and its real
Cauchy majorant fixed canonically. -/
noncomputable def cmp116Eq214CauchyMajorizedResummation
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (analyticData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214AnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Ψ Φ E)
    (boundaryMajorant :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ) :
    CMP116HResummation
      (Finset (FinBox d N'))
      (Finset (Finset (FinBox d N')))
      (Finset (PhysicalBond d (M * N')))
      (Finset (FinBox d N')) ιZ0' Ψ Φ :=
  cmp116Eq214AnalyticResummation domainFamily allowed ambient distinguished
    Z0PrimeIndex analyticData
    (fun Z D P Z0 Z0p =>
      cmp116Eq214CauchyTermWeight (analyticData Z D P Z0 Z0p)
        (boundaryMajorant Z D P Z0 Z0p))

@[simp] theorem cmp116Eq214CauchyMajorizedResummation_termWeight
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Ψ Φ E : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (analyticData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214AnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Ψ Φ E)
    (boundaryMajorant :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) (Z0p : ιZ0') :
    (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
      distinguished Z0PrimeIndex analyticData boundaryMajorant).termWeight
        Z D P Z0 Z0p =
      cmp116Eq214CauchyTermWeight (analyticData Z D P Z0 Z0p)
        (boundaryMajorant Z D P Z0 Z0p) := by
  rfl

/-- The contour estimate discharges the generic pointwise `hterm` obligation
for the canonically majorized resummation. -/
theorem cmp116Eq214CauchyMajorizedResummation_term_bound
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Ψ Φ E : Type*} [DecidableEq ιZ0']
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (analyticData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214AnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Ψ Φ E)
    (boundaryMajorant :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (hDelta : ∀ Z D P Z0 Z0p i,
      0 < (analyticData Z D P Z0 Z0p).deltaRadius i)
    (hY : ∀ Z D P Z0 Z0p i,
      0 < (analyticData Z D P Z0 Z0p).yRadius i)
    (hcontour : ∀ Z D P Z0 Z0p ψ φ,
      CMP116Eq214NestedCauchyBoundaryBound nDelta nY
        (analyticData Z D P Z0 Z0p).deltaRadius
        (analyticData Z D P Z0 Z0p).yRadius
        (fun sigma tau =>
          (analyticData Z D P Z0 Z0p).analyticIntegrand
            (cmp116Eq214SmallFieldBondCarrier ambient distinguished D)
            P sigma tau ψ φ)
        (boundaryMajorant Z D P Z0 Z0p)) :
    ∀ Z x,
      x ∈ cmp116HIndexFinset
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData boundaryMajorant) Z →
      ∀ ψ φ,
        ‖(cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData boundaryMajorant).summand
            Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
            distinguished Z0PrimeIndex analyticData boundaryMajorant).termWeight
              Z x.1.1 x.1.2 x.2.1 x.2.2 := by
  intro Z x _hx ψ φ
  exact (analyticData Z x.1.1 x.1.2 x.2.1 x.2.2).norm_term_le_cauchyRate
    (cmp116Eq214SmallFieldBondCarrier ambient distinguished x.1.1)
    x.1.2 ψ φ (boundaryMajorant Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hDelta Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hY Z x.1.1 x.1.2 x.2.1 x.2.2)
    (hcontour Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ)

/-- Source-facing finite resummation bound with no arbitrary summand and no
arbitrary term weight.  The remaining budget is the genuine geometric and
analytic summation problem of (2.16)--(2.26). -/
theorem norm_balabanCMP116H_le_of_cauchyMajorants
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Ψ Φ E : Type*} [DecidableEq ιZ0']
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (hp : CMP116Lemma3Parameters)
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (analyticData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214AnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Ψ Φ E)
    (boundaryMajorant :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (sourceMetric : Finset (FinBox d N') → ℕ)
    (hDelta : ∀ Z D P Z0 Z0p i,
      0 < (analyticData Z D P Z0 Z0p).deltaRadius i)
    (hY : ∀ Z D P Z0 Z0p i,
      0 < (analyticData Z D P Z0 Z0p).yRadius i)
    (hcontour : ∀ Z D P Z0 Z0p ψ φ,
      CMP116Eq214NestedCauchyBoundaryBound nDelta nY
        (analyticData Z D P Z0 Z0p).deltaRadius
        (analyticData Z D P Z0 Z0p).yRadius
        (fun sigma tau =>
          (analyticData Z D P Z0 Z0p).analyticIntegrand
            (cmp116Eq214SmallFieldBondCarrier ambient distinguished D)
            P sigma tau ψ φ)
        (boundaryMajorant Z D P Z0 Z0p))
    (hbudget : ∀ Z,
      Finset.sum (cmp116HIndexFinset
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData boundaryMajorant) Z)
        (fun x => cmp116Eq214CauchyTermWeight
          (analyticData Z x.1.1 x.1.2 x.2.1 x.2.2)
          (boundaryMajorant Z x.1.1 x.1.2 x.2.1 x.2.2)) ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
            sourceMetric Z) :
    ∀ Z ψ φ,
      ‖balabanCMP116H
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData boundaryMajorant) Z ψ φ‖ ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
            sourceMetric Z := by
  apply norm_balabanCMP116H_le_termWeightSum hp
    (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
      distinguished Z0PrimeIndex analyticData boundaryMajorant)
    sourceMetric
  · exact cmp116Eq214CauchyMajorizedResummation_term_bound
      domainFamily allowed ambient distinguished Z0PrimeIndex analyticData
      boundaryMajorant hDelta hY hcontour
  · intro Z
    simpa using hbudget Z

end YangMills.RG
