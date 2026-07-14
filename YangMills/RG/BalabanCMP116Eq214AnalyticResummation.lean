/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalResummation
import YangMills.RG.BalabanCMP116Eq214PhysicalTerm

/-!
# CMP116 equation (2.14): analytic summands on the physical index stack

This module removes the arbitrary complex `summand` from the physical
`D/P/Z₀` resummation.  Every summand is now definitionally the nested Cauchy
and Gaussian term recorded in `CMP116Eq214AnalyticData.term`.

The only analytic field left free in the `CMP116HResummation` record is the
real `termWeight`.  That is deliberate: producing this majorant is exactly the
termwise estimate (2.26), and it must not be hidden in a construction record.

For the cutoff decomposition, `Y₀` at bond level is the complement inside the
declared ambient family of the literal exterior carrier `Y₀^{c,*}`.  Thus it
also retains the distinguished bonds removed from `Y₀^{c,*}`.
-/

namespace YangMills.RG

open Finset
open scoped BigOperators

/-- Bond family on which the `χ_{k,Y₀}` factor of (2.14) is evaluated. -/
noncomputable def cmp116Eq214SmallFieldBondCarrier {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    Finset (PhysicalBond d (M * N')) :=
  ambient \ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D

@[simp] theorem mem_cmp116Eq214SmallFieldBondCarrier_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {e : PhysicalBond d (M * N')} :
    e ∈ cmp116Eq214SmallFieldBondCarrier ambient distinguished D ↔
      e ∈ ambient ∧
        e ∉ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D := by
  classical
  simp [cmp116Eq214SmallFieldBondCarrier]

/-- The small-field and exterior carriers partition the ambient bond family. -/
theorem cmp116Eq214_smallField_union_outside {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    cmp116Eq214SmallFieldBondCarrier ambient distinguished D ∪
        cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D =
      ambient := by
  classical
  apply Finset.sdiff_union_of_subset
  intro e he
  exact (mem_cmp116Eq23PhysicalBondOutsideCarrier_iff.mp he).1

/-- The two bond carriers used in the cutoff expansion are disjoint. -/
theorem cmp116Eq214_disjoint_smallField_outside {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    Disjoint (cmp116Eq214SmallFieldBondCarrier ambient distinguished D)
      (cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D) := by
  classical
  simp [Finset.disjoint_left, cmp116Eq214SmallFieldBondCarrier]

/-- The physical resummation with its complex summand fixed literally by
equation (2.14). -/
noncomputable def cmp116Eq214AnalyticResummation
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
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ) :
    CMP116HResummation
      (Finset (FinBox d N'))
      (Finset (Finset (FinBox d N')))
      (Finset (PhysicalBond d (M * N')))
      (Finset (FinBox d N')) ιZ0' Ψ Φ :=
  cmp116Eq214PhysicalResummation domainFamily allowed ambient distinguished
    Z0PrimeIndex
    (fun Z D P Z0 Z0p ψ φ =>
      (analyticData Z D P Z0 Z0p).term
        (cmp116Eq214SmallFieldBondCarrier ambient distinguished D) P ψ φ)
    termWeight

/-- Projection of a physical analytic resummation to its literal (2.14)
summand. -/
@[simp] theorem cmp116Eq214AnalyticResummation_summand
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
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) (Z0p : ιZ0') (ψ : Ψ) (φ : Φ) :
    (cmp116Eq214AnalyticResummation domainFamily allowed ambient distinguished
      Z0PrimeIndex analyticData termWeight).summand Z D P Z0 Z0p ψ φ =
      (analyticData Z D P Z0 Z0p).term
        (cmp116Eq214SmallFieldBondCarrier ambient distinguished D) P ψ φ := by
  rfl

/-- Consequently `H(Z)` is literally a finite sum of equation-(2.14) terms
over the physical dependent index stack. -/
theorem balabanCMP116H_eq_sum_physicalTerms
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
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N')) (ψ : Ψ) (φ : Φ) :
    balabanCMP116H
        (cmp116Eq214AnalyticResummation domainFamily allowed ambient distinguished
          Z0PrimeIndex analyticData termWeight) Z ψ φ =
      ∑ x ∈ cmp116HIndexFinset
          (cmp116Eq214AnalyticResummation domainFamily allowed ambient distinguished
            Z0PrimeIndex analyticData termWeight) Z,
        (analyticData Z x.1.1 x.1.2 x.2.1 x.2.2).term
          (cmp116Eq214SmallFieldBondCarrier ambient distinguished x.1.1)
          x.1.2 ψ φ := by
  rfl

end YangMills.RG
