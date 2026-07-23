/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalAnalyticData

/-!
# CMP116 equation (2.14): source-faithful local activity identification

This module assembles the type-local equation-(2.14) terms over the existing
physical dependent index stack.  The resulting `LocalActivity` is not defined
from the value of `balabanCMP116H` after the fact: each summand is first built
from restricted physical weights, and only then are the summands added.

Its global evaluation is exactly the analytic resummation already used by the
quantitative campaign.  Thus the activity-identification equality and the
finite support of `H(Z)` are consequences of one source-facing construction.
-/

namespace YangMills.RG

open Finset

noncomputable section

/-- The analytic resummation obtained by forgetting the restricted fields in
each local physical term. -/
def cmp116Eq214LocalAnalyticResummation
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (localData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214LocalAnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Site Psi Phi E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ) :
    CMP116HResummation
      (Finset (FinBox d N'))
      (Finset (Finset (FinBox d N')))
      (Finset (PhysicalBond d (M * N')))
      (Finset (FinBox d N')) ιZ0'
      (∀ s, Psi s) (∀ s, Phi s) :=
  cmp116Eq214AnalyticResummation domainFamily allowed ambient distinguished
    Z0PrimeIndex
    (fun Z D P Z0 Z0p => (localData Z D P Z0 Z0p).toAnalyticData)
    termWeight

/-- The physical `H(Z)` as a finite sum of genuinely local equation-(2.14)
activities. -/
def cmp116Eq214LocalHActivity
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} [DecidableEq ιZ0'] [DecidableEq Site]
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (localData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214LocalAnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Site Psi Phi E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N')) : LocalActivity Site Psi Phi ℂ :=
  let R := cmp116Eq214LocalAnalyticResummation domainFamily allowed ambient
    distinguished Z0PrimeIndex localData termWeight
  LocalActivity.finsetSum (cmp116HIndexFinset R Z) fun x =>
    (localData Z x.1.1 x.1.2 x.2.1 x.2.2).localTerm
      (cmp116Eq214SmallFieldBondCarrier ambient distinguished x.1.1) x.1.2

/-- The local construction evaluates to the pre-existing literal analytic
resummation.  This is the source-faithful `activity_identification` endpoint. -/
@[simp] theorem globalEval_cmp116Eq214LocalHActivity
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} [DecidableEq ιZ0'] [DecidableEq Site]
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (localData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214LocalAnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Site Psi Phi E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N')) (psi : ∀ s, Psi s) (phi : ∀ s, Phi s) :
    (cmp116Eq214LocalHActivity domainFamily allowed ambient distinguished
        Z0PrimeIndex localData termWeight Z).globalEval psi phi =
      balabanCMP116H
        (cmp116Eq214LocalAnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex localData termWeight) Z psi phi := by
  rw [cmp116Eq214LocalHActivity, LocalActivity.globalEval_finsetSum]
  rfl

/-- A common source support bound for the local summands bounds the spectator
support of the assembled `H(Z)` activity. -/
theorem spectatorSupport_cmp116Eq214LocalHActivity_subset
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} [DecidableEq ιZ0'] [DecidableEq Site]
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (localData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214LocalAnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Site Psi Phi E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (spectatorSupport : Finset (FinBox d N') → Finset Site)
    (hsupport : ∀ Z x,
      x ∈ cmp116HIndexFinset
        (cmp116Eq214LocalAnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex localData termWeight) Z →
      (localData Z x.1.1 x.1.2 x.2.1 x.2.2).spectatorSupport ⊆
        spectatorSupport Z)
    (Z : Finset (FinBox d N')) :
    (cmp116Eq214LocalHActivity domainFamily allowed ambient distinguished
      Z0PrimeIndex localData termWeight Z).spectatorSupport ⊆
        spectatorSupport Z := by
  apply LocalActivity.spectatorSupport_finsetSum_subset
  intro x hx
  exact hsupport Z x hx

/-- The analogous common support bound for the fluctuation field. -/
theorem fluctuationSupport_cmp116Eq214LocalHActivity_subset
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} [DecidableEq ιZ0'] [DecidableEq Site]
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (localData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214LocalAnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B Site Psi Phi E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (fluctuationSupport : Finset (FinBox d N') → Finset Site)
    (hsupport : ∀ Z x,
      x ∈ cmp116HIndexFinset
        (cmp116Eq214LocalAnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex localData termWeight) Z →
      (localData Z x.1.1 x.1.2 x.2.1 x.2.2).fluctuationSupport ⊆
        fluctuationSupport Z)
    (Z : Finset (FinBox d N')) :
    (cmp116Eq214LocalHActivity domainFamily allowed ambient distinguished
      Z0PrimeIndex localData termWeight Z).fluctuationSupport ⊆
        fluctuationSupport Z := by
  apply LocalActivity.fluctuationSupport_finsetSum_subset
  intro x hx
  exact hsupport Z x hx

end

end YangMills.RG
