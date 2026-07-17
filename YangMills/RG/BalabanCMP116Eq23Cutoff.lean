/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# CMP116 equation (2.3): the large-field inclusion--exclusion index

Balaban CMP 116, page 12, equation (2.3), decomposes the small-field cutoff
outside the distinguished region `Y₀` as a finite sum over subsets `P`:

`χₖ = χₖ,Y₀ * χₖ,Y₀ᶜ,* =
  ∑ P ⊆ Y₀ᶜ,* , (-1)^|P| * χₖ,Y₀ * χᶜₖ,P`.

Here `χᶜₖ,P` is the product of the large-field indicators
`1_{ε₁/gₖ ≤ ‖B(b)‖}` over `b ∈ P`.  This module makes the physical `P` index
literal: it is the powerset of the finite carrier `Y₀ᶜ,*`, not an abstract
summation type.  The proof is the finite product inclusion--exclusion identity
`Finset.prod_sub` after proving that the small- and large-field indicators are
complements.

The same cutoff appears in CMP 109, equation (2.9).  This file constructs the
finite carrier `Y₀ᶜ,*` from explicit ambient and distinguished bond families.
It does not yet identify those generic families, the gauge-field norm, or the
scale ratio `ε₁/gₖ` with the corresponding objects in the CMP116 source
hierarchy; those are the next dictionary obligations for the literal term
(2.14).
-/

namespace YangMills.RG

open scoped BigOperators

/-- The small-field factor on one bond, with the CMP116 threshold supplied
explicitly (eventually `ε₁ / gₖ`). -/
noncomputable def cmp116SmallFieldIndicator
    {E : Type*} [Norm E] (threshold : ℝ) (x : E) : ℂ :=
  if ‖x‖ < threshold then 1 else 0

/-- The complementary large-field factor on one bond. -/
noncomputable def cmp116LargeFieldIndicator
    {E : Type*} [Norm E] (threshold : ℝ) (x : E) : ℂ :=
  if threshold ≤ ‖x‖ then 1 else 0

/-- The two CMP116 bond cutoffs are literal complementary indicators. -/
theorem cmp116SmallFieldIndicator_eq_one_sub_large
    {E : Type*} [Norm E] (threshold : ℝ) (x : E) :
    cmp116SmallFieldIndicator threshold x =
      1 - cmp116LargeFieldIndicator threshold x := by
  by_cases h : ‖x‖ < threshold
  · have hnle : ¬ threshold ≤ ‖x‖ := not_le_of_gt h
    simp [cmp116SmallFieldIndicator, cmp116LargeFieldIndicator, h, hnle]
  · have hle : threshold ≤ ‖x‖ := le_of_not_gt h
    simp [cmp116SmallFieldIndicator, cmp116LargeFieldIndicator, h, hle]

/-- Product small-field cutoff on a finite family of bonds. -/
noncomputable def cmp116SmallFieldCutoff
    {β E : Type*} [Norm E] (carrier : Finset β)
    (threshold : ℝ) (B : β → E) : ℂ :=
  ∏ b ∈ carrier, cmp116SmallFieldIndicator threshold (B b)

/-- `χᶜₖ,P`: product large-field cutoff on the selected bonds `P`. -/
noncomputable def cmp116LargeFieldCutoff
    {β E : Type*} [Norm E] (P : Finset β)
    (threshold : ℝ) (B : β → E) : ℂ :=
  ∏ b ∈ P, cmp116LargeFieldIndicator threshold (B b)

/-- The physical finite index family for `P` in CMP116 equation (2.3). -/
def cmp116Eq23PIndex {β : Type*} [DecidableEq β]
    (outsideCarrier : Finset β) : Finset (Finset β) :=
  outsideCarrier.powerset

@[simp] theorem mem_cmp116Eq23PIndex_iff
    {β : Type*} [DecidableEq β] {P outsideCarrier : Finset β} :
    P ∈ cmp116Eq23PIndex outsideCarrier ↔ P ⊆ outsideCarrier := by
  simp [cmp116Eq23PIndex]

/-- Inclusion--exclusion for the cutoff on the exterior bond carrier. -/
theorem cmp116SmallFieldCutoff_eq_sum_powerset_large
    {β E : Type*} [DecidableEq β] [Norm E] (outsideCarrier : Finset β)
    (threshold : ℝ) (B : β → E) :
    cmp116SmallFieldCutoff outsideCarrier threshold B =
      ∑ P ∈ cmp116Eq23PIndex outsideCarrier,
        (-1 : ℂ) ^ P.card * cmp116LargeFieldCutoff P threshold B := by
  classical
  simp_rw [cmp116SmallFieldCutoff, cmp116SmallFieldIndicator_eq_one_sub_large]
  rw [Finset.prod_sub]
  simp [cmp116Eq23PIndex, cmp116LargeFieldCutoff]

/-- CMP116 equation (2.3), with `Y₀` and `Y₀ᶜ,*` supplied as finite bond
carriers and the physical threshold supplied explicitly.

This is the exact finite decomposition that supplies the `PIndex`, its sign,
and its cutoff factor to the future literal summand (2.14). -/
theorem cmp116Eq23_cutoff_decomposition
    {β E : Type*} [DecidableEq β] [Norm E] (Y0 outsideCarrier : Finset β)
    (threshold : ℝ) (B : β → E) :
    cmp116SmallFieldCutoff Y0 threshold B *
        cmp116SmallFieldCutoff outsideCarrier threshold B =
      ∑ P ∈ cmp116Eq23PIndex outsideCarrier,
        (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff Y0 threshold B *
            cmp116LargeFieldCutoff P threshold B := by
  rw [cmp116SmallFieldCutoff_eq_sum_powerset_large outsideCarrier threshold B]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  ring

/-- The CMP116 region `Y₀ = ⋃_{Y ∈ D} Y`, for a finite family `D` of finite
bond regions. -/
def cmp116Eq23Y0 {β : Type*} [DecidableEq β]
    (D : Finset (Finset β)) : Finset β :=
  D.biUnion fun Y => Y

@[simp] theorem mem_cmp116Eq23Y0_iff
    {β : Type*} [DecidableEq β] {D : Finset (Finset β)} {b : β} :
    b ∈ cmp116Eq23Y0 D ↔ ∃ Y ∈ D, b ∈ Y := by
  simp [cmp116Eq23Y0]

/-- The literal exterior carrier `Y₀ᶜ,*` from CMP116 equation (2.3), relative
to a finite ambient bond set.  The second subtraction removes the distinguished
bonds `b₀(c)` used by the source decomposition. -/
def cmp116Eq23OutsideCarrier {β : Type*} [DecidableEq β]
    (ambient distinguished : Finset β) (D : Finset (Finset β)) : Finset β :=
  (ambient \ cmp116Eq23Y0 D) \ distinguished

@[simp] theorem mem_cmp116Eq23OutsideCarrier_iff
    {β : Type*} [DecidableEq β]
    {ambient distinguished : Finset β} {D : Finset (Finset β)} {b : β} :
    b ∈ cmp116Eq23OutsideCarrier ambient distinguished D ↔
      b ∈ ambient ∧ b ∉ cmp116Eq23Y0 D ∧ b ∉ distinguished := by
  simp [cmp116Eq23OutsideCarrier, and_assoc]

/-- The source-shaped `P` family after deriving both `Y₀` and `Y₀ᶜ,*` from
the finite region family `D`. -/
def cmp116Eq23PhysicalPIndex {β : Type*} [DecidableEq β]
    (ambient distinguished : Finset β) (D : Finset (Finset β)) :
    Finset (Finset β) :=
  cmp116Eq23PIndex (cmp116Eq23OutsideCarrier ambient distinguished D)

@[simp] theorem mem_cmp116Eq23PhysicalPIndex_iff
    {β : Type*} [DecidableEq β]
    {ambient distinguished : Finset β} {D : Finset (Finset β)} {P : Finset β} :
    P ∈ cmp116Eq23PhysicalPIndex ambient distinguished D ↔
      P ⊆ cmp116Eq23OutsideCarrier ambient distinguished D := by
  simp [cmp116Eq23PhysicalPIndex]

/-- Equation (2.3) with `Y₀`, `Y₀ᶜ,*`, and the `P`-summation family derived
from the physical finite-region data. -/
theorem cmp116Eq23_physicalCutoffDecomposition
    {β E : Type*} [DecidableEq β] [Norm E]
    (ambient distinguished : Finset β) (D : Finset (Finset β))
    (threshold : ℝ) (B : β → E) :
    cmp116SmallFieldCutoff (cmp116Eq23Y0 D) threshold B *
        cmp116SmallFieldCutoff
          (cmp116Eq23OutsideCarrier ambient distinguished D) threshold B =
      ∑ P ∈ cmp116Eq23PhysicalPIndex ambient distinguished D,
        (-1 : ℂ) ^ P.card *
          cmp116SmallFieldCutoff (cmp116Eq23Y0 D) threshold B *
            cmp116LargeFieldCutoff P threshold B := by
  exact cmp116Eq23_cutoff_decomposition
    (cmp116Eq23Y0 D)
    (cmp116Eq23OutsideCarrier ambient distinguished D) threshold B

end YangMills.RG
