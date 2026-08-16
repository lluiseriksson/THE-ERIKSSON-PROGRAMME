/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatMultidimensionalDFT

/-!
# Exact finite-grid aliasing for absolutely summable Fourier coefficients

PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the Lean compiler.

The remaining CMP99 finite-to-continuous bridge must not identify a finite
DFT with a Brillouin integral by definition.  This module isolates the exact
algebraic part of that bridge.  An integer Fourier frequency is reduced into
the finite reciprocal box, character orthogonality selects one residue class,
and absolute summability justifies exchanging the finite grid sum with the
infinite Fourier series.

The physical Fourier-series expansion is deliberately not accepted or
asserted here.  A later source-specific module must construct it from the
literal CMP89 Brillouin coefficients and their sealed exponential bound.
Consequently this module does not identify the generated Green, construct
regional `B0`, attain window 15, discharge a terminal field or inhabit
`TermSource`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Coordinatewise reduction of an integer Fourier frequency into the
finite reciprocal box. -/
def cmp99FlatIntegerResidue {d N : ℕ}
    (u : Fin d → ℤ) : CMP99FlatZModBox d N :=
  fun mu => (u mu : ZMod N)

/-- Integer frequencies in one fixed finite-grid residue class. -/
abbrev CMP99FlatIntegerResidueClass
    (d N : ℕ) (r : CMP99FlatZModBox d N) :=
  {u : Fin d → ℤ // cmp99FlatIntegerResidue (N := N) u = r}

/-- Every product character has unit norm. -/
theorem norm_cmp99FlatZModFourierCharacter
    {d N : ℕ} [NeZero N]
    (k x : CMP99FlatZModBox d N) :
    ‖cmp99FlatZModFourierCharacter k x‖ = 1 := by
  unfold cmp99FlatZModFourierCharacter
  rw [norm_prod]
  simp [ZMod.stdAddChar_apply]

/-- The normalized finite-grid character average selects exactly one residue
class of integer frequencies. -/
theorem cmp99Flat_normalizedCharacterAverage_integerResidue
    {d N : ℕ} [NeZero N]
    (r : CMP99FlatZModBox d N) (u : Fin d → ℤ) :
    ((N : ℂ) ^ d)⁻¹ *
        (∑ k : CMP99FlatZModBox d N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp99FlatZModFourierCharacter k
              (cmp99FlatIntegerResidue (N := N) u)) =
      if cmp99FlatIntegerResidue (N := N) u = r then 1 else 0 := by
  have hcard : (N : ℂ) ^ d ≠ 0 :=
    pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hsum := sum_cmp99FlatZModFourierCharacter_mul_neg
    (cmp99FlatIntegerResidue (N := N) u) r
  calc
    ((N : ℂ) ^ d)⁻¹ *
          (∑ k : CMP99FlatZModBox d N,
            cmp99FlatZModFourierCharacter (-k) r *
              cmp99FlatZModFourierCharacter k
                (cmp99FlatIntegerResidue (N := N) u)) =
        ((N : ℂ) ^ d)⁻¹ *
          (∑ k : CMP99FlatZModBox d N,
            cmp99FlatZModFourierCharacter k
                (cmp99FlatIntegerResidue (N := N) u) *
              cmp99FlatZModFourierCharacter (-k) r) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ((N : ℂ) ^ d)⁻¹ *
          (if cmp99FlatIntegerResidue (N := N) u = r then
            (N : ℂ) ^ d else 0) := by rw [hsum]
    _ = if cmp99FlatIntegerResidue (N := N) u = r then 1 else 0 := by
      by_cases h : cmp99FlatIntegerResidue (N := N) u = r
      · simp [h, hcard]
      · simp [h]

/-- Absolutely summable integer coefficients define a pointwise absolutely
summable finite-grid Fourier series. -/
theorem summable_cmp99FlatZModFourierCharacter_mul_integerCoefficient
    {d N : ℕ} [NeZero N]
    {coefficient : (Fin d → ℤ) → ℂ}
    (hcoefficient : Summable coefficient)
    (k : CMP99FlatZModBox d N) :
    Summable (fun u : Fin d → ℤ =>
      cmp99FlatZModFourierCharacter k
          (cmp99FlatIntegerResidue (N := N) u) * coefficient u) := by
  apply Summable.of_norm_bounded hcoefficient.norm
  intro u
  rw [norm_mul, norm_cmp99FlatZModFourierCharacter, one_mul]

/-- Fourier series sampled on the exact finite reciprocal grid.  The series
is only a generic algebraic object here; the physical CMP89 integrand must be
identified with it downstream. -/
def cmp99FlatFiniteGridFourierSeriesSample
    {d N : ℕ} [NeZero N]
    (coefficient : (Fin d → ℤ) → ℂ)
    (k : CMP99FlatZModBox d N) : ℂ :=
  ∑' u : Fin d → ℤ,
    cmp99FlatZModFourierCharacter k
        (cmp99FlatIntegerResidue (N := N) u) * coefficient u

/-- **Finite-grid aliasing / periodization.**  The normalized discrete
Fourier coefficient of an absolutely summable continuous Fourier series is
the sum of precisely those continuous coefficients in the selected residue
class.  No physical Fourier-series equality is a premise of this theorem. -/
theorem cmp99Flat_normalizedFiniteGridFourierSeriesSample_eq_residueClass
    {d N : ℕ} [NeZero N]
    (coefficient : (Fin d → ℤ) → ℂ)
    (hcoefficient : Summable coefficient)
    (r : CMP99FlatZModBox d N) :
    ((N : ℂ) ^ d)⁻¹ *
        ∑ k : CMP99FlatZModBox d N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp99FlatFiniteGridFourierSeriesSample coefficient k =
      ∑' u : CMP99FlatIntegerResidueClass d N r, coefficient u := by
  let term := fun k : CMP99FlatZModBox d N =>
    fun u : Fin d → ℤ =>
      cmp99FlatZModFourierCharacter (-k) r *
        (cmp99FlatZModFourierCharacter k
          (cmp99FlatIntegerResidue (N := N) u) * coefficient u)
  have hterm : ∀ k : CMP99FlatZModBox d N, Summable (term k) := by
    intro k
    apply Summable.of_norm_bounded hcoefficient.norm
    intro u
    simp only [term, norm_mul,
      norm_cmp99FlatZModFourierCharacter, one_mul]
    exact le_rfl
  have hdistribute : ∀ k : CMP99FlatZModBox d N,
      cmp99FlatZModFourierCharacter (-k) r *
          cmp99FlatFiniteGridFourierSeriesSample coefficient k =
        ∑' u : Fin d → ℤ, term k u := by
    intro k
    rw [cmp99FlatFiniteGridFourierSeriesSample, tsum_mul_left]
  have hswap :
      (∑' u : Fin d → ℤ,
          ∑ k : CMP99FlatZModBox d N, term k u) =
        ∑ k : CMP99FlatZModBox d N, ∑' u : Fin d → ℤ, term k u := by
    simpa using Summable.tsum_finsetSum
      (s := (Finset.univ : Finset (CMP99FlatZModBox d N)))
      (f := fun k u => term k u)
      (fun k _ => hterm k)
  simp_rw [hdistribute]
  calc
    ((N : ℂ) ^ d)⁻¹ *
          ∑ k : CMP99FlatZModBox d N, ∑' u : Fin d → ℤ, term k u =
        ((N : ℂ) ^ d)⁻¹ *
          ∑' u : Fin d → ℤ,
            ∑ k : CMP99FlatZModBox d N, term k u := by rw [hswap]
    _ = ∑' u : Fin d → ℤ,
          ((N : ℂ) ^ d)⁻¹ *
            ∑ k : CMP99FlatZModBox d N, term k u := by
          rw [tsum_mul_left]
    _ = ∑' u : Fin d → ℤ,
          Set.indicator
            {u | cmp99FlatIntegerResidue (N := N) u = r}
            coefficient u := by
          apply tsum_congr
          intro u
          rw [Set.indicator_apply]
          have hselector :=
            cmp99Flat_normalizedCharacterAverage_integerResidue r u
          change ((N : ℂ) ^ d)⁻¹ *
              (∑ k : CMP99FlatZModBox d N,
                cmp99FlatZModFourierCharacter (-k) r *
                  (cmp99FlatZModFourierCharacter k
                    (cmp99FlatIntegerResidue (N := N) u) *
                      coefficient u)) = _
          have hfactor :
              (∑ k : CMP99FlatZModBox d N,
                cmp99FlatZModFourierCharacter (-k) r *
                  (cmp99FlatZModFourierCharacter k
                    (cmp99FlatIntegerResidue (N := N) u) *
                      coefficient u)) =
                (∑ k : CMP99FlatZModBox d N,
                  cmp99FlatZModFourierCharacter (-k) r *
                    cmp99FlatZModFourierCharacter k
                      (cmp99FlatIntegerResidue (N := N) u)) *
                    coefficient u := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [hfactor]
          rw [show ((N : ℂ) ^ d)⁻¹ *
              ((∑ k : CMP99FlatZModBox d N,
                cmp99FlatZModFourierCharacter (-k) r *
                  cmp99FlatZModFourierCharacter k
                    (cmp99FlatIntegerResidue (N := N) u)) *
                coefficient u) =
              (((N : ℂ) ^ d)⁻¹ *
                ∑ k : CMP99FlatZModBox d N,
                  cmp99FlatZModFourierCharacter (-k) r *
                    cmp99FlatZModFourierCharacter k
                      (cmp99FlatIntegerResidue (N := N) u)) *
                coefficient u by ring]
          rw [hselector]
          by_cases h : cmp99FlatIntegerResidue (N := N) u = r
          · simp [h]
          · simp [h]
    _ = ∑' u : CMP99FlatIntegerResidueClass d N r, coefficient u :=
      (tsum_subtype
        {u | cmp99FlatIntegerResidue (N := N) u = r} coefficient).symm

end

end YangMills.RG
