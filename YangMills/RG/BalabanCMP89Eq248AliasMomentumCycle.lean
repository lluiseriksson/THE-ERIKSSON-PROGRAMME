/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq245CenteredAliasVectorCycle
import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicity

/-!
# PRE-VALIDATION: physical-period transport of CMP89 alias momentum

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

CMP89 (2.45) integrates over the physical Brillouin cube and sums over a
centered finite reciprocal-alias fibre. Shifting one physical momentum
coordinate by `2*pi` therefore advances the corresponding alias coordinate.
Away from the upper representative this is literal equality of alias
momenta. At the wrap, the two momenta differ by the larger pointwise period
`2*pi*N`.

This module proves that disjunction from the already sealed vector cycle. It
then gives a generic transport theorem for any factor whose pointwise
`2*pi*N` period has been proved, and reindexes its complete finite alias sum.
No amplitude, Laplacian, denominator or full integrand periodicity is assumed
or claimed here.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Shift one physical momentum coordinate by the Brillouin period `2*pi`. -/
def cmp89Eq248PhysicalCoordinatePeriodShift {d : ℕ}
    (mu : Fin d) (z : Fin d → ℂ) : Fin d → ℂ :=
  z + Pi.single mu (((2 * Real.pi : ℝ) : ℂ))

/-- After a physical `2*pi` shift, one alias momentum is either the momentum
at the cycled representative or its explicit `2*pi*N` pointwise-period
translate at the wrap. -/
theorem cmp89Eq248EntireAliasMomentum_physicalShift_cycle_or_wrap
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    cmp89Eq248EntireAliasMomentum
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1 =
        cmp89Eq248EntireAliasMomentum z
          (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1 ∨
      cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1 =
        cmp89Eq251CoordinateAliasPeriodShift N mu
          (cmp89Eq248EntireAliasMomentum z
            (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1) := by
  rcases cmp89Eq245CenteredAliasVectorCycle_value_or_wrap d N hN mu m with
    hnowrap | hwrap
  · left
    funext nu
    by_cases hnu : nu = mu
    · subst nu
      have hC := congrArg (fun x : ℤ => (x : ℂ)) hnowrap
      push_cast at hC
      simp [cmp89Eq248EntireAliasMomentum,
        cmp89Eq248PhysicalCoordinatePeriodShift,
        cmp89Eq245AliasShift, Pi.single_apply]
      linear_combination -(2 * (Real.pi : ℂ)) * hC
    · have hfix := cmp89Eq245CenteredAliasVectorCycle_apply_of_ne
        d N hN mu nu hnu m
      simp [cmp89Eq248EntireAliasMomentum,
        cmp89Eq248PhysicalCoordinatePeriodShift,
        cmp89Eq245AliasShift, Pi.single_apply, hnu, hfix]
  · right
    funext nu
    by_cases hnu : nu = mu
    · subst nu
      have hC := congrArg (fun x : ℤ => (x : ℂ)) hwrap
      push_cast at hC
      simp [cmp89Eq248EntireAliasMomentum,
        cmp89Eq248PhysicalCoordinatePeriodShift,
        cmp89Eq251CoordinateAliasPeriodShift,
        cmp89Eq245AliasShift, Pi.single_apply]
      linear_combination -(2 * (Real.pi : ℂ)) * hC
    · have hfix := cmp89Eq245CenteredAliasVectorCycle_apply_of_ne
        d N hN mu nu hnu m
      simp [cmp89Eq248EntireAliasMomentum,
        cmp89Eq248PhysicalCoordinatePeriodShift,
        cmp89Eq251CoordinateAliasPeriodShift,
        cmp89Eq245AliasShift, Pi.single_apply, hnu, hfix]

/-- A factor with proved pointwise alias period `2*pi*N` transports across
the physical `2*pi` shift by cycling the centered representative. -/
theorem cmp89Eq248AliasFactor_physicalShift_eq_cycle
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ)
    {A : Type*} (F : (Fin d → ℂ) → A)
    (hperiod : ∀ q,
      F (cmp89Eq251CoordinateAliasPeriodShift N mu q) = F q)
    (m : {m : Fin d → ℤ // m ∈ cmp89Eq245CenteredAliasVectors d N}) :
    F (cmp89Eq248EntireAliasMomentum
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1) =
      F (cmp89Eq248EntireAliasMomentum z
        (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1) := by
  rcases cmp89Eq248EntireAliasMomentum_physicalShift_cycle_or_wrap
      hN mu z m with hdirect | hwrap
  · rw [hdirect]
  · rw [hwrap, hperiod]

/-- Reindex the subtype sum of a pointwise alias-periodic factor after the
physical `2*pi` shift. -/
theorem cmp89Eq248AliasFactor_physicalShift_subtypeSum_eq
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ)
    {A : Type*} [AddCommMonoid A] (F : (Fin d → ℂ) → A)
    (hperiod : ∀ q,
      F (cmp89Eq251CoordinateAliasPeriodShift N mu q) = F q) :
    (∑ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d N},
      F (cmp89Eq248EntireAliasMomentum
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1)) =
      ∑ m : {m : Fin d → ℤ //
        m ∈ cmp89Eq245CenteredAliasVectors d N},
        F (cmp89Eq248EntireAliasMomentum z m.1) := by
  calc
    _ = ∑ m : {m : Fin d → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors d N},
        F (cmp89Eq248EntireAliasMomentum z
          (cmp89Eq245CenteredAliasVectorCycle d N hN mu m).1) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact cmp89Eq248AliasFactor_physicalShift_eq_cycle
        hN mu z F hperiod m
    _ = _ := Equiv.sum_comp
      (cmp89Eq245CenteredAliasVectorCycle d N hN mu)
      (fun m => F (cmp89Eq248EntireAliasMomentum z m.1))

/-- Consumer-facing finite-sum version on the literal alias finset printed
in CMP89 (2.45). -/
theorem cmp89Eq248AliasFactor_physicalShift_finsetSum_eq
    {d N : ℕ} (hN : 0 < N) (mu : Fin d) (z : Fin d → ℂ)
    {A : Type*} [AddCommMonoid A] (F : (Fin d → ℂ) → A)
    (hperiod : ∀ q,
      F (cmp89Eq251CoordinateAliasPeriodShift N mu q) = F q) :
    (∑ m ∈ cmp89Eq245CenteredAliasVectors d N,
      F (cmp89Eq248EntireAliasMomentum
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m)) =
      ∑ m ∈ cmp89Eq245CenteredAliasVectors d N,
        F (cmp89Eq248EntireAliasMomentum z m) := by
  calc
    _ = ∑ m : {m : Fin d → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors d N},
        F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m.1) :=
      (Finset.sum_coe_sort
        (cmp89Eq245CenteredAliasVectors d N)
        (fun m => F (cmp89Eq248EntireAliasMomentum
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m))).symm
    _ = ∑ m : {m : Fin d → ℤ //
          m ∈ cmp89Eq245CenteredAliasVectors d N},
        F (cmp89Eq248EntireAliasMomentum z m.1) :=
      cmp89Eq248AliasFactor_physicalShift_subtypeSum_eq
        hN mu z F hperiod
    _ = _ := Finset.sum_coe_sort
      (cmp89Eq245CenteredAliasVectors d N)
      (fun m => F (cmp89Eq248EntireAliasMomentum z m))

end

end YangMills.RG
