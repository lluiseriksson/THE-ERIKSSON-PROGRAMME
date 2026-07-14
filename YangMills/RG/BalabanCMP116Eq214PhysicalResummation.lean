/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalIndices
import YangMills.RG.BalabanCMP116Lemma3

/-!
# CMP116 equation (2.14): physical resummation index stack

`CMP116HResummation` is the finite dependent-sum interface consumed by the
Lemma-3 bounds.  Until this module its `D/P/Z₀` index functions could remain
abstract.  Here they are instantiated by the physical families constructed
from equations (2.2)--(2.3) and the least-domain condition on printed page 12.

The `Z₀'` family, the complex summand, and its real majorant remain explicit
inputs because their identification belongs to the later random-walk and
termwise analytic parts of equation (2.14).  No one-point or post-hoc index is
used: the first three levels are the literal finite physical families.

The terminal membership theorem expands one element of the flattened Lemma-3
index into all source-side clauses for `D`, `P`, and `Z₀`.
-/

namespace YangMills.RG

open Finset

/-- The physical `D/P/Z₀` instantiation of the generic CMP116 resummation. -/
noncomputable def cmp116Eq214PhysicalResummation
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*}
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ) :
    CMP116HResummation
      (Finset (FinBox d N'))
      (Finset (Finset (FinBox d N')))
      (Finset (PhysicalBond d (M * N')))
      (Finset (FinBox d N')) ιZ0' Ψ Φ where
  DIndex Z := cmp116Eq214DIndex domainFamily Z
  PIndex _Z D := cmp116Eq214PIndex ambient distinguished D
  Z0Index Z D P := cmp116Eq214Z0Index allowed Z D P
  Z0PrimeIndex := Z0PrimeIndex
  summand := summand
  termWeight := termWeight

@[simp] theorem cmp116Eq214PhysicalResummation_DIndex
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*}
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N')) :
    (cmp116Eq214PhysicalResummation domainFamily allowed ambient distinguished
      Z0PrimeIndex summand termWeight).DIndex Z =
      cmp116Eq214DIndex domainFamily Z := by
  rfl

@[simp] theorem cmp116Eq214PhysicalResummation_PIndex
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*}
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N'))) :
    (cmp116Eq214PhysicalResummation domainFamily allowed ambient distinguished
      Z0PrimeIndex summand termWeight).PIndex Z D =
      cmp116Eq214PIndex ambient distinguished D := by
  rfl

@[simp] theorem cmp116Eq214PhysicalResummation_Z0Index
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*}
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    (cmp116Eq214PhysicalResummation domainFamily allowed ambient distinguished
      Z0PrimeIndex summand termWeight).Z0Index Z D P =
      cmp116Eq214Z0Index allowed Z D P := by
  rfl

/-- Membership in the flattened resummation is exactly membership at every
level of the physical dependent index stack. -/
theorem mem_cmp116Eq214PhysicalResummation_index_iff
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*} [DecidableEq ιZ0']
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) (Z0p : ιZ0') :
    ((D, P), (Z0, Z0p)) ∈
        cmp116HIndexFinset
          (cmp116Eq214PhysicalResummation domainFamily allowed
            ambient distinguished Z0PrimeIndex summand termWeight) Z ↔
      D ∈ cmp116Eq214DIndex domainFamily Z ∧
      P ∈ cmp116Eq214PIndex ambient distinguished D ∧
      Z0 ∈ cmp116Eq214Z0Index allowed Z D P ∧
      Z0p ∈ Z0PrimeIndex Z D P Z0 := by
  classical
  simp [cmp116HIndexFinset, cmp116Eq214PhysicalResummation]

/-- Fully expanded physical membership clauses for a flattened equation
(2.14) resummation index. -/
theorem mem_cmp116Eq214PhysicalResummation_index_iff_source
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ : Type*} [DecidableEq ιZ0']
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (summand :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → Ψ → Φ → ℂ)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) (Z0p : ιZ0') :
    ((D, P), (Z0, Z0p)) ∈
        cmp116HIndexFinset
          (cmp116Eq214PhysicalResummation domainFamily allowed
            ambient distinguished Z0PrimeIndex summand termWeight) Z ↔
      D ⊆ domainFamily ∧
      cmp116Eq23Y0 D ⊆ Z ∧
      P ⊆ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D ∧
      CMP116LeastAllowedLocalizationDomain allowed Z D P Z0 ∧
      Z0p ∈ Z0PrimeIndex Z D P Z0 := by
  rw [mem_cmp116Eq214PhysicalResummation_index_iff]
  simp only [mem_cmp116Eq214DIndex_iff, mem_cmp116Eq214PIndex_iff,
    mem_cmp116Eq214Z0Index_iff]
  tauto

end YangMills.RG
