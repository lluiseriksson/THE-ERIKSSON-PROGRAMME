/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceScaledStratification
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint

/-!
# The printed coefficients in the CMP99 source mass

Printed CMP99 (3.24), p. 394, uses the coefficient

`a_j (L^j eta)^(d-2)`

on `Lambda_j`, with

`a_0 = a` and `a_{j+1} = a a_j / (a L^(-2) + a_j)`.

This file formalizes that recurrence, proves positivity from `a,L,eta > 0`,
and inserts the exact coefficient into the dependent-lattice mass.  In
particular no unweighted counting adjoint or terminal-scale coefficient is
silently reused.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u v w

/-- The source recurrence for the mass parameters `a_j` below (3.24). -/
def cmp99SourceMassParameter (a L : ℝ) : ℕ → ℝ
  | 0 => a
  | j + 1 =>
      a * cmp99SourceMassParameter a L j /
        (a * (L ^ 2)⁻¹ + cmp99SourceMassParameter a L j)

@[simp] theorem cmp99SourceMassParameter_zero (a L : ℝ) :
    cmp99SourceMassParameter a L 0 = a := rfl

@[simp] theorem cmp99SourceMassParameter_succ (a L : ℝ) (j : ℕ) :
    cmp99SourceMassParameter a L (j + 1) =
      a * cmp99SourceMassParameter a L j /
        (a * (L ^ 2)⁻¹ + cmp99SourceMassParameter a L j) := rfl

/-- Positivity of every recursively generated source coefficient. -/
theorem cmp99SourceMassParameter_pos
    {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    ∀ j, 0 < cmp99SourceMassParameter a L j := by
  intro j
  induction j with
  | zero => simpa using ha
  | succ j ih =>
      rw [cmp99SourceMassParameter_succ]
      have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
      exact div_pos (mul_pos ha ih)
        (add_pos (mul_pos ha (inv_pos.mpr hLsq)) ih)

/-- The literal coefficient `a_j (L^j eta)^(d-2)` in (3.24). -/
def cmp99SourceStratumWeight
    (d : ℕ) (a L eta : ℝ) (j : ℕ) : ℝ :=
  cmp99SourceMassParameter a L j *
    (L ^ j * eta) ^ (d - 2)

/-- The source coefficient is positive in the physical parameter regime. -/
theorem cmp99SourceStratumWeight_pos
    (d : ℕ) {a L eta : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (j : ℕ) :
    0 < cmp99SourceStratumWeight d a L eta j := by
  rw [cmp99SourceStratumWeight]
  exact mul_pos (cmp99SourceMassParameter_pos ha hL j)
    (pow_pos (mul_pos (pow_pos hL j) heta) _)

/-- The source coefficient indexed by the finite family of strata. -/
def cmp99SourceFiniteStratumWeight
    {n : ℕ} (d : ℕ) (a L eta : ℝ) (r : Fin n) : ℝ :=
  cmp99SourceStratumWeight d a L eta r.val

theorem cmp99SourceFiniteStratumWeight_pos
    {n : ℕ} (d : ℕ) {a L eta : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (r : Fin n) :
    0 < cmp99SourceFiniteStratumWeight (n := n) d a L eta r :=
  cmp99SourceStratumWeight_pos d ha hL heta r.val

/-- Coefficient of the mass operator when represented in Lean's counting
Hilbert structure.  Multiplication by the source pairing weight `eta^d`
recovers the printed coefficient in (3.24). -/
def cmp99SourceCountingStratumWeight
    {n : ℕ} (d : ℕ) (a L eta : ℝ) (r : Fin n) : ℝ :=
  cmp99SourceFiniteStratumWeight d a L eta r / eta ^ d

/-- The counting-Hilbert coefficient is strictly positive under the printed
positive source parameters. -/
theorem cmp99SourceCountingStratumWeight_pos
    {n : ℕ} (d : ℕ) {a L eta : ℝ}
    (ha : 0 < a) (hL : 0 < L) (heta : 0 < eta) (r : Fin n) :
    0 < cmp99SourceCountingStratumWeight d a L eta r := by
  exact div_pos
    (cmp99SourceFiniteStratumWeight_pos d ha hL heta r)
    (pow_pos heta d)

/-- The corrected source precision, represented in the counting Hilbert
structure,

`Delta_U^eta + Q'^* a Q'`

with the complete dependent-lattice quadratic form of (3.24). -/
noncomputable def cmp99SourceScaledGaugePrecision
    {FineSite : Type u} [DecidableEq FineSite]
    {n : ℕ} {ScaleSite : Fin n → Type v}
    [∀ r, DecidableEq (ScaleSite r)] [∀ r, Fintype (ScaleSite r)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (covariantLaplacian : E →L[ℝ] E)
    (Qprime : ∀ r,
      E →L[ℝ]
        CMP99SourceScaledStratification.ScaleField
          (ScaleSite := ScaleSite) g r)
    (d : ℕ) (a L eta : ℝ) : E →L[ℝ] E :=
  covariantLaplacian +
    S.sourceGaugeMass Qprime
      (cmp99SourceCountingStratumWeight d a L eta)

/-- Exact source-spacing quadratic form of the source precision
(3.23)--(3.24).  The hypothesis `eta != 0` is precisely what converts the
counting representation back to the printed `eta^d` pairing. -/
theorem spacingPairing_cmp99SourceScaledGaugePrecision
    {FineSite : Type u} [DecidableEq FineSite]
    {n : ℕ} {ScaleSite : Fin n → Type v}
    [∀ r, DecidableEq (ScaleSite r)] [∀ r, Fintype (ScaleSite r)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (covariantLaplacian : E →L[ℝ] E)
    (Qprime : ∀ r,
      E →L[ℝ]
        CMP99SourceScaledStratification.ScaleField
          (ScaleSite := ScaleSite) g r)
    (d : ℕ) (a L eta : ℝ) (heta : eta ≠ 0) (phi : E) :
    cmp99SourceSpacingPairing d eta phi
        (cmp99SourceScaledGaugePrecision S covariantLaplacian Qprime
          d a L eta phi) =
      cmp99SourceSpacingPairing d eta phi (covariantLaplacian phi) +
        ∑ r : Fin n,
          cmp99SourceMassParameter a L r.val *
            (L ^ r.val * eta) ^ (d - 2) *
              ∑ y ∈ S.strata r, ‖Qprime r phi y‖ ^ 2 := by
  rw [cmp99SourceSpacingPairing, cmp99SourceScaledGaugePrecision,
    ContinuousLinearMap.add_apply, inner_add_right,
    CMP99SourceScaledStratification.inner_sourceGaugeMass]
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [cmp99SourceCountingStratumWeight,
    cmp99SourceFiniteStratumWeight, cmp99SourceStratumWeight]
  have hetaPow : eta ^ d ≠ 0 := pow_ne_zero d heta
  field_simp

end

end YangMills.RG
