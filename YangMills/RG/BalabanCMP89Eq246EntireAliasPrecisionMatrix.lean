/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq248ComplexAliasDenominator

/-!
# Entire alias-fibre precision matrix in CMP89 (2.44)--(2.47)

PRE-VALIDATION: source is present, the `.olean` has not yet been materialized,
and these declarations have not yet been verified by the Lean compiler.

CMP89 (2.44)--(2.46) becomes, at fixed coarse momentum, a finite system on
the reciprocal-lattice aliases.  Its matrix is the diagonal fine-lattice
symbol plus the rank-one block-averaging term

`diag (Delta_l) + a * u_l * u_{-m}`.

This is the source-faithful object on which the complex-strip argument must be
made.  The quotients displayed after solving the system may have removable
singularities alias by alias; the matrix itself has entire entries and does
not demand separate nonvanishing of every `Delta_l`.

The module constructs the literal matrix, proves its exact action, proves
entrywise holomorphy, and identifies the opposite-momentum row with complex
conjugation on the real slice.  It does not prove invertibility, a uniform
complex strip, a strip bound `B0`, contour displacement, or the physical
regional-Green dictionary.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- The finite reciprocal-lattice alias fibre printed in CMP89 (2.45). -/
abbrev CMP89Eq246AliasIndex (d L j : ℕ) :=
  ↑(cmp89Eq245CenteredAliasVectors d (L ^ j))

/-- Fine-lattice diagonal entry `Delta^xi(p+l)` in the alias fibre. -/
def cmp89Eq246EntireAliasFineSymbol
    (d L j : ℕ) (mass : ℝ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) : ℂ :=
  cmp89Eq245EntireScaledLaplacianSymbol
    d (((L : ℝ) ^ j)⁻¹) mass
    (cmp89Eq248EntireAliasMomentum z m.1)

/-- Column factor `u_j(p+l)` of the rank-one averaging term. -/
def cmp89Eq246EntireAliasAverageColumn
    (d L j : ℕ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) : ℂ :=
  cmp89Eq245EntireAverageAmplitude d (L ^ j)
    (cmp89Eq248EntireAliasMomentum z m.1)

/-- Holomorphic opposite-momentum row factor replacing complex conjugation. -/
def cmp89Eq246EntireAliasAverageRow
    (d L j : ℕ) (z : Fin d → ℂ)
    (m : CMP89Eq246AliasIndex d L j) : ℂ :=
  cmp89Eq245EntireAverageAmplitude d (L ^ j)
    (-cmp89Eq248EntireAliasMomentum z m.1)

/-- The entire finite alias-fibre precision matrix behind CMP89 (2.46).

The first term is the diagonal Fourier symbol of `-Δ^ξ + m_j²`; the
second is the literal rank-one fibre of `a_j Q_jᵀ Q_j`. -/
def cmp89Eq246EntireAliasPrecisionMatrix
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ) :
    Matrix (CMP89Eq246AliasIndex d L j)
      (CMP89Eq246AliasIndex d L j) ℂ :=
  fun m n =>
    (if m = n then cmp89Eq246EntireAliasFineSymbol d L j mass z m else 0) +
      (a : ℂ) * cmp89Eq246EntireAliasAverageColumn d L j z m *
        cmp89Eq246EntireAliasAverageRow d L j z n

/-- Exact diagonal-plus-rank-one action of the source precision matrix. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec
    (d L j : ℕ) (mass a : ℝ) (z : Fin d → ℂ)
    (phi : CMP89Eq246AliasIndex d L j → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec phi m =
      cmp89Eq246EntireAliasFineSymbol d L j mass z m * phi m +
        (a : ℂ) * cmp89Eq246EntireAliasAverageColumn d L j z m *
          ∑ n, cmp89Eq246EntireAliasAverageRow d L j z n * phi n := by
  classical
  simp only [cmp89Eq246EntireAliasPrecisionMatrix, Matrix.mulVec, dotProduct,
    add_mul, Finset.sum_add_distrib]
  have hdiagonal :
      (∑ x,
        (if m = x then cmp89Eq246EntireAliasFineSymbol d L j mass z m else 0) *
          phi x) =
        cmp89Eq246EntireAliasFineSymbol d L j mass z m * phi m := by
    simpa only [ite_mul, zero_mul] using
      (Fintype.sum_ite_eq m
        (fun x => cmp89Eq246EntireAliasFineSymbol d L j mass z m * phi x))
  rw [hdiagonal]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Every matrix entry is entire in the coarse complex momentum. -/
theorem differentiable_cmp89Eq246EntireAliasPrecisionMatrix_entry
    (d L j : ℕ) (mass a : ℝ)
    (m n : CMP89Eq246AliasIndex d L j) :
    Differentiable ℂ
      (fun z : Fin d → ℂ =>
        cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z m n) := by
  have hshiftM : Differentiable ℂ
      (fun z : Fin d → ℂ => cmp89Eq248EntireAliasMomentum z m.1) := by
    unfold cmp89Eq248EntireAliasMomentum
    fun_prop
  have hshiftN : Differentiable ℂ
      (fun z : Fin d → ℂ => -cmp89Eq248EntireAliasMomentum z n.1) := by
    unfold cmp89Eq248EntireAliasMomentum
    fun_prop
  have hfine : Differentiable ℂ
      (fun z : Fin d → ℂ =>
        cmp89Eq246EntireAliasFineSymbol d L j mass z m) := by
    exact
      (differentiable_cmp89Eq245EntireScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass).comp hshiftM
  have hcolumn : Differentiable ℂ
      (fun z : Fin d → ℂ =>
        cmp89Eq246EntireAliasAverageColumn d L j z m) := by
    exact
      (differentiable_cmp89Eq245EntireAverageAmplitude d (L ^ j)).comp hshiftM
  have hrow : Differentiable ℂ
      (fun z : Fin d → ℂ =>
        cmp89Eq246EntireAliasAverageRow d L j z n) := by
    exact
      (differentiable_cmp89Eq245EntireAverageAmplitude d (L ^ j)).comp hshiftN
  by_cases hmn : m = n
  · simpa only [cmp89Eq246EntireAliasPrecisionMatrix, hmn, if_pos] using
      hfine.add ((hcolumn.const_mul (a : ℂ)).mul hrow)
  · simpa only [cmp89Eq246EntireAliasPrecisionMatrix, hmn, if_neg,
      if_false, zero_add] using
      ((hcolumn.const_mul (a : ℂ)).mul hrow)

/-- On the real slice, the holomorphic row factor is the complex conjugate of
the physical column factor. -/
theorem cmp89Eq246EntireAliasAverageRow_ofReal_eq_conj
    (d L j : ℕ) (p : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasAverageRow d L j (fun mu => (p mu : ℂ)) m =
      starRingEnd ℂ
        (cmp89Eq246EntireAliasAverageColumn
          d L j (fun mu => (p mu : ℂ)) m) := by
  let q : Fin d → ℝ := fun mu => p mu + cmp89Eq245AliasShift m.1 mu
  have halias :
      cmp89Eq248EntireAliasMomentum (fun mu => (p mu : ℂ)) m.1 =
        fun mu => (q mu : ℂ) := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, q]
  rw [cmp89Eq246EntireAliasAverageRow,
    cmp89Eq246EntireAliasAverageColumn, halias]
  exact cmp89Eq245EntireAverageAmplitude_neg_ofReal_eq_conj d (L ^ j) q

/-- On the real slice, each diagonal entry is the literal nonnegative fine
symbol at the corresponding reciprocal alias. -/
theorem cmp89Eq246EntireAliasFineSymbol_ofReal_eq
    (d L j : ℕ) (mass : ℝ) (p : Fin d → ℝ)
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasFineSymbol d L j mass
        (fun mu => (p mu : ℂ)) m =
      (cmp89Eq245ScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass
        (fun mu => p mu + cmp89Eq245AliasShift m.1 mu) : ℂ) := by
  have halias :
      cmp89Eq248EntireAliasMomentum (fun mu => (p mu : ℂ)) m.1 =
        fun mu => ((p mu + cmp89Eq245AliasShift m.1 mu : ℝ) : ℂ) := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum]
  rw [cmp89Eq246EntireAliasFineSymbol, halias,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq]

end

end YangMills.RG
