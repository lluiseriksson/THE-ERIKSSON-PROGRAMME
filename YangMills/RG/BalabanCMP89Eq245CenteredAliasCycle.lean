/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq250FullDenominatorLower

/-!
# PRE-VALIDATION: centered CMP89 alias cycle

The source is present, its `.olean` has not yet been materialized, and the
result has not yet been verified by the compiler.

CMP89 (2.45) uses the centered half-open set of `N = L^j` reciprocal aliases
in each coordinate. A physical momentum shift by `2*pi` does not fix an
individual representative: it cyclically permutes this centered fibre. This
module constructs that permutation without identifying the physical period
`2*pi` with the larger pointwise period `2*pi*N`.

The wrap is kept explicit. Away from the upper endpoint the new integer is
`m + 1`; at the upper endpoint it is the lower representative, so adding `N`
recovers `m + 1`. No periodicity of the complete CMP89 integrand is claimed
here; the average, Laplacian, denominator, and phase factors still require
their separate transport lemmas.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- The lower endpoint of the centered alias interval. -/
def cmp89Eq245CenteredAliasLower (N : ℕ) : ℤ :=
  -((N / 2 : ℕ) : ℤ)

/-- The parity split printed in CMP89 (2.45) is uniformly the half-open
interval of `N` consecutive integers beginning at `-floor(N/2)`. -/
theorem cmp89Eq245CenteredAliasIntegers_eq_Ico (N : ℕ) :
    cmp89Eq245CenteredAliasIntegers N =
      Finset.Ico (cmp89Eq245CenteredAliasLower N)
        (cmp89Eq245CenteredAliasLower N + (N : ℤ)) := by
  rw [cmp89Eq245CenteredAliasIntegers]
  split_ifs with hEven
  · rcases hEven with ⟨k, hk⟩
    ext m
    simp only [Finset.mem_Ico]
    simp only [cmp89Eq245CenteredAliasLower]
    omega
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨k, hk⟩
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    simp only [cmp89Eq245CenteredAliasLower]
    omega

/-- Move one step to the right in the centered alias interval, wrapping its
upper endpoint to the lower endpoint. -/
def cmp89Eq245CenteredAliasSucc
    (N : ℕ) (hN : 0 < N)
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N}) :
    {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N} :=
  if h : m.1 + 1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) then
    ⟨m.1 + 1, by
      have hm : cmp89Eq245CenteredAliasLower N ≤ m.1 ∧
          m.1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
          Finset.mem_Ico] using m.property
      have hout : cmp89Eq245CenteredAliasLower N ≤ m.1 + 1 ∧
          m.1 + 1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        omega
      simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
        Finset.mem_Ico] using hout⟩
  else
    ⟨cmp89Eq245CenteredAliasLower N, by
      have hNint : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
      have hout : cmp89Eq245CenteredAliasLower N ≤
            cmp89Eq245CenteredAliasLower N ∧
          cmp89Eq245CenteredAliasLower N <
            cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        omega
      simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
        Finset.mem_Ico] using hout⟩

/-- Move one step to the left in the centered alias interval, wrapping its
lower endpoint to the upper endpoint minus one. -/
def cmp89Eq245CenteredAliasPred
    (N : ℕ) (hN : 0 < N)
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N}) :
    {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N} :=
  if h : cmp89Eq245CenteredAliasLower N < m.1 then
    ⟨m.1 - 1, by
      have hm : cmp89Eq245CenteredAliasLower N ≤ m.1 ∧
          m.1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
          Finset.mem_Ico] using m.property
      have hout : cmp89Eq245CenteredAliasLower N ≤ m.1 - 1 ∧
          m.1 - 1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        omega
      simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
        Finset.mem_Ico] using hout⟩
  else
    ⟨cmp89Eq245CenteredAliasLower N + (N : ℤ) - 1, by
      have hNint : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
      have hout : cmp89Eq245CenteredAliasLower N ≤
            cmp89Eq245CenteredAliasLower N + (N : ℤ) - 1 ∧
          cmp89Eq245CenteredAliasLower N + (N : ℤ) - 1 <
            cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
        omega
      simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
        Finset.mem_Ico] using hout⟩

/-- Predecessor is a left inverse of successor on the centered fibre. -/
theorem cmp89Eq245CenteredAliasPred_succ
    (N : ℕ) (hN : 0 < N)
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N}) :
    cmp89Eq245CenteredAliasPred N hN
        (cmp89Eq245CenteredAliasSucc N hN m) = m := by
  apply Subtype.ext
  have hm : cmp89Eq245CenteredAliasLower N ≤ m.1 ∧
      m.1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
    simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
      Finset.mem_Ico] using m.property
  change (cmp89Eq245CenteredAliasPred N hN
      (cmp89Eq245CenteredAliasSucc N hN m)).1 = m.1
  dsimp only [cmp89Eq245CenteredAliasSucc, cmp89Eq245CenteredAliasPred]
  split_ifs <;> omega

/-- Successor is a left inverse of predecessor on the centered fibre. -/
theorem cmp89Eq245CenteredAliasSucc_pred
    (N : ℕ) (hN : 0 < N)
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N}) :
    cmp89Eq245CenteredAliasSucc N hN
        (cmp89Eq245CenteredAliasPred N hN m) = m := by
  apply Subtype.ext
  have hm : cmp89Eq245CenteredAliasLower N ≤ m.1 ∧
      m.1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
    simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
      Finset.mem_Ico] using m.property
  change (cmp89Eq245CenteredAliasSucc N hN
      (cmp89Eq245CenteredAliasPred N hN m)).1 = m.1
  dsimp only [cmp89Eq245CenteredAliasSucc, cmp89Eq245CenteredAliasPred]
  split_ifs <;> omega

/-- The cyclic permutation of one centered reciprocal-alias coordinate. -/
def cmp89Eq245CenteredAliasCycle
    (N : ℕ) (hN : 0 < N) :
    Equiv.Perm {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N} where
  toFun := cmp89Eq245CenteredAliasSucc N hN
  invFun := cmp89Eq245CenteredAliasPred N hN
  left_inv := cmp89Eq245CenteredAliasPred_succ N hN
  right_inv := cmp89Eq245CenteredAliasSucc_pred N hN

/-- The cycle advances by one without wrap, or by one modulo the literal
alias count `N` at the upper endpoint. -/
theorem cmp89Eq245CenteredAliasCycle_value_or_wrap
    (N : ℕ) (hN : 0 < N)
    (m : {m : ℤ // m ∈ cmp89Eq245CenteredAliasIntegers N}) :
    (cmp89Eq245CenteredAliasCycle N hN m).1 = m.1 + 1 ∨
      (cmp89Eq245CenteredAliasCycle N hN m).1 + (N : ℤ) = m.1 + 1 := by
  have hm : cmp89Eq245CenteredAliasLower N ≤ m.1 ∧
      m.1 < cmp89Eq245CenteredAliasLower N + (N : ℤ) := by
    simpa only [cmp89Eq245CenteredAliasIntegers_eq_Ico,
      Finset.mem_Ico] using m.property
  change (cmp89Eq245CenteredAliasSucc N hN m).1 = m.1 + 1 ∨
    (cmp89Eq245CenteredAliasSucc N hN m).1 + (N : ℤ) = m.1 + 1
  dsimp only [cmp89Eq245CenteredAliasSucc]
  split_ifs <;> omega

end

end YangMills.RG
