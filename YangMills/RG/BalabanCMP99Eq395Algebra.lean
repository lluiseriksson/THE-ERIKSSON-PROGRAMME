/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The noncommutative algebra in CMP99 equation (3.95)

On printed p. 411, CMP99 writes `A = Q' G'^2 Q'^*` and decomposes

`A C0 = I + sum_D (T1(D) + T2(D) + T3(D)) = I - R`,

where

* `T1 = (1 - chi) A h C h`,
* `T2 = chi (A - A_D) h C h`, and
* `T3 = [chi A_D, h] C h`.

This file proves the exact cancellation in an arbitrary noncommutative ring.
It then shows that the displayed equation follows from two strictly smaller
physical identities: the local-covariance partition sums to `C0`, and the
localized inverse pieces resolve the identity.  Neither premise renames
(3.95), and no commutation of operator factors is assumed.
-/

namespace YangMills.RG

open scoped BigOperators

universe u v

section Local

variable {E : Type u} [Ring E]

/-- First sum of CMP99 (3.95), for one localization cube. -/
def cmp99Eq395FirstTerm (A chi h C : E) : E :=
  (1 - chi) * A * (h * C * h)

/-- Second sum of CMP99 (3.95), for one localization cube. -/
def cmp99Eq395SecondTerm (A AD chi h C : E) : E :=
  chi * (A - AD) * (h * C * h)

/-- Third, commutator sum of CMP99 (3.95), for one localization cube. -/
def cmp99Eq395ThirdTerm (AD chi h C : E) : E :=
  (chi * AD * h - h * (chi * AD)) * C * h

/-- The three displayed summands cancel locally without commuting any pair of
operators. -/
theorem cmp99Eq395_threeTerms_eq
    (A AD chi h C : E) :
    cmp99Eq395FirstTerm A chi h C +
        cmp99Eq395SecondTerm A AD chi h C +
        cmp99Eq395ThirdTerm AD chi h C =
      A * (h * C * h) - h * (chi * AD) * C * h := by
  simp only [cmp99Eq395FirstTerm, cmp99Eq395SecondTerm,
    cmp99Eq395ThirdTerm]
  noncomm_ring

end Local

section FiniteFamily

variable {Index : Type v} {E : Type u} [Ring E]

/-- The complete correction sum printed on the right of CMP99 (3.95). -/
def cmp99Eq395Correction (domains : Finset Index)
    (A : E) (AD chi h C : Index → E) : E :=
  ∑ D ∈ domains,
    (cmp99Eq395FirstTerm A (chi D) (h D) (C D) +
      cmp99Eq395SecondTerm A (AD D) (chi D) (h D) (C D) +
      cmp99Eq395ThirdTerm (AD D) (chi D) (h D) (C D))

/-- Summing the local cancellation separates the two physical partition
identities needed for (3.95). -/
theorem cmp99Eq395Correction_eq
    (domains : Finset Index) (A : E) (AD chi h C : Index → E) :
    cmp99Eq395Correction domains A AD chi h C =
      A * (∑ D ∈ domains, h D * C D * h D) -
        ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D := by
  rw [cmp99Eq395Correction]
  calc
    ∑ D ∈ domains,
        (cmp99Eq395FirstTerm A (chi D) (h D) (C D) +
          cmp99Eq395SecondTerm A (AD D) (chi D) (h D) (C D) +
          cmp99Eq395ThirdTerm (AD D) (chi D) (h D) (C D)) =
        ∑ D ∈ domains,
          (A * (h D * C D * h D) -
            h D * (chi D * AD D) * C D * h D) := by
      apply Finset.sum_congr rfl
      intro D _hD
      exact cmp99Eq395_threeTerms_eq A (AD D) (chi D) (h D) (C D)
    _ = (∑ D ∈ domains, A * (h D * C D * h D)) -
          ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D := by
      rw [Finset.sum_sub_distrib]
    _ = A * (∑ D ∈ domains, h D * C D * h D) -
          ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D := by
      rw [Finset.mul_sum]

/-- One localized inverse term in (3.95) reduces to the square of its smooth
partition multiplier.  The proof uses only the support identity `h * chi = h`
and the genuine local inverse identity `AD * C = 1`; it assumes no commutation
between the four factors. -/
theorem cmp99Eq395_local_resolution_term
    (AD chi h C : E)
    (hsupport : h * chi = h)
    (hinverse : AD * C = 1) :
    h * (chi * AD) * C * h = h * h := by
  calc
    h * (chi * AD) * C * h = (h * chi) * (AD * C) * h := by
      noncomm_ring
    _ = h * h := by rw [hsupport, hinverse, mul_one]

/-- Global-carrier form of the localized resolution.  A regional inverse
extended by zero satisfies `AD * C = proj`, not `AD * C = 1`; this regional
projector may be larger than the source characteristic `chi`.  The two
support identities for the smooth cutoff turn the projected inverse into the
same square-partition term. -/
theorem cmp99Eq395_local_resolution_term_of_projected_inverse
    (AD chi proj h C : E)
    (hsupport : h * chi = h)
    (hregion : h * proj = h)
    (hinverse : AD * C = proj) :
    h * (chi * AD) * C * h = h * h := by
  calc
    h * (chi * AD) * C * h = (h * chi) * (AD * C) * h := by
      noncomm_ring
    _ = h * h := by rw [hinverse, hsupport, hregion]

/-- The localized inverse pieces resolve the identity once the smooth
partition is square-normalized.  This derives the `hresolution` premise below
from the three source-level ingredients that actually produce it. -/
theorem cmp99Eq395_resolution_of_local_inverses
    (domains : Finset Index) (AD chi h C : Index → E)
    (hsupport : ∀ D ∈ domains, h D * chi D = h D)
    (hinverse : ∀ D ∈ domains, AD D * C D = 1)
    (hsquare : ∑ D ∈ domains, h D * h D = 1) :
    ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D = 1 := by
  calc
    (∑ D ∈ domains, h D * (chi D * AD D) * C D * h D) =
        ∑ D ∈ domains, h D * h D := by
      apply Finset.sum_congr rfl
      intro D hD
      exact cmp99Eq395_local_resolution_term
        (AD D) (chi D) (h D) (C D) (hsupport D hD) (hinverse D hD)
    _ = 1 := hsquare

/-- The source-faithful global resolution generated by zero-extended
regional inverses.  Each local product is its regional projector rather than
the ambient identity or, in general, the smaller source characteristic. -/
theorem cmp99Eq395_resolution_of_projected_local_inverses
    (domains : Finset Index) (AD chi proj h C : Index → E)
    (hsupport : ∀ D ∈ domains, h D * chi D = h D)
    (hregion : ∀ D ∈ domains, h D * proj D = h D)
    (hinverse : ∀ D ∈ domains, AD D * C D = proj D)
    (hsquare : ∑ D ∈ domains, h D * h D = 1) :
    ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D = 1 := by
  calc
    (∑ D ∈ domains, h D * (chi D * AD D) * C D * h D) =
        ∑ D ∈ domains, h D * h D := by
      apply Finset.sum_congr rfl
      intro D hD
      exact cmp99Eq395_local_resolution_term_of_projected_inverse
        (AD D) (chi D) (proj D) (h D) (C D)
        (hsupport D hD) (hregion D hD) (hinverse D hD)
    _ = 1 := hsquare

/-- Source-facing form of (3.95).  The premises are exactly the two local
operator identities exposed by the cancellation, rather than (3.95) itself. -/
theorem cmp99Eq395_of_partition_identities
    (domains : Finset Index) (A C0 : E) (AD chi h C : Index → E)
    (hcovariance : ∑ D ∈ domains, h D * C D * h D = C0)
    (hresolution :
      ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D = 1) :
    A * C0 = 1 + cmp99Eq395Correction domains A AD chi h C := by
  rw [cmp99Eq395Correction_eq, hcovariance, hresolution]
  noncomm_ring

/-- The sign convention in the final equality `I - R` of (3.95). -/
def cmp99Eq395R (domains : Finset Index)
    (A : E) (AD chi h C : Index → E) : E :=
  -cmp99Eq395Correction domains A AD chi h C

/-- Exact final orientation of the source display. -/
theorem cmp99Eq395_eq_one_sub_R
    (domains : Finset Index) (A C0 : E) (AD chi h C : Index → E)
    (hcovariance : ∑ D ∈ domains, h D * C D * h D = C0)
    (hresolution :
      ∑ D ∈ domains, h D * (chi D * AD D) * C D * h D = 1) :
    A * C0 = 1 - cmp99Eq395R domains A AD chi h C := by
  rw [cmp99Eq395R, sub_neg_eq_add]
  exact cmp99Eq395_of_partition_identities domains A C0 AD chi h C
    hcovariance hresolution

/-- Fully decomposed source-facing producer for (3.95).  The covariance sum,
support of the smooth cutoffs, local inverse identities, and square partition
are all visible separately; the localized resolution is generated internally. -/
theorem cmp99Eq395_eq_one_sub_R_of_local_inverses
    (domains : Finset Index) (A C0 : E) (AD chi h C : Index → E)
    (hcovariance : ∑ D ∈ domains, h D * C D * h D = C0)
    (hsupport : ∀ D ∈ domains, h D * chi D = h D)
    (hinverse : ∀ D ∈ domains, AD D * C D = 1)
    (hsquare : ∑ D ∈ domains, h D * h D = 1) :
    A * C0 = 1 - cmp99Eq395R domains A AD chi h C := by
  apply cmp99Eq395_eq_one_sub_R domains A C0 AD chi h C hcovariance
  exact cmp99Eq395_resolution_of_local_inverses
    domains AD chi h C hsupport hinverse hsquare

/-- Fully decomposed source-facing producer for (3.95) on one common ambient
carrier.  Regional covariance inverses are extended by zero, so their exact
product is the corresponding regional projector. -/
theorem cmp99Eq395_eq_one_sub_R_of_projected_local_inverses
    (domains : Finset Index) (A C0 : E) (AD chi proj h C : Index → E)
    (hcovariance : ∑ D ∈ domains, h D * C D * h D = C0)
    (hsupport : ∀ D ∈ domains, h D * chi D = h D)
    (hregion : ∀ D ∈ domains, h D * proj D = h D)
    (hinverse : ∀ D ∈ domains, AD D * C D = proj D)
    (hsquare : ∑ D ∈ domains, h D * h D = 1) :
    A * C0 = 1 - cmp99Eq395R domains A AD chi h C := by
  apply cmp99Eq395_eq_one_sub_R domains A C0 AD chi h C hcovariance
  exact cmp99Eq395_resolution_of_projected_local_inverses
    domains AD chi proj h C hsupport hregion hinverse hsquare

end FiniteFamily

end YangMills.RG
