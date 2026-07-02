/-
# Word-side Catalan closure for rooted child-factorial weights

This module proves the algebraic word-sum half of
`YangMills.KP.RootedChildFactorialCatalanIdentity`.

For a word `s : Fin L -> Fin (m + 1)`, `cnt s v` counts the occurrences of
`v`, and `wt s` is `(cnt s 0 + 1)` times the product of the factorials
`(cnt s v)!` over all letters `v`.

The main entry points are:

* `sum_wt_mul_factorial`, the exact factorial closed form for the total
  weight over words of length `L`;
* `word_sum_eq`, the Catalan specialization
  `sum wt = n! * catalan n` for words of length `n - 1`;
* `word_sum_normalized`, the corresponding normalized real identity.

The remaining repo-facing obligation is not proved here: one still needs the
tree-to-word bridge identifying the weighted sum over complete-graph spanning
trees, using `rootedChildCount`, with the word sum proved in this file.  Once
that bridge is available, `word_sum_normalized` composes directly with the
existing `rootedChildFactorialTreeSumNormalized` interface.

Checked target: Lean `leanprover/lean4:v4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`.

Expected oracle for the three main theorems:
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

open Finset Nat

namespace RootedTreeCatalan

variable {m L : ℕ}

/-- Ocurrencias de la letra `v` en la palabra `s : Fin L → Fin (m+1)`
(el «perfil de multiplicidad» `a_v` de la reducción de Prüfer). -/
def cnt (s : Fin L → Fin (m + 1)) (v : Fin (m + 1)) : ℕ :=
  ∑ i, if s i = v then 1 else 0

/-- Peso Prüfer de una palabra:
`wt s = (a₀ + 1) · ∏_v a_v! = (a₀+1)! · ∏_{v≠0} a_v!`,
que bajo Prüfer es exactamente el peso de árbol `∏_v c_T(v)!`. -/
def wt (s : Fin L → Fin (m + 1)) : ℕ :=
  (cnt s 0 + 1) * ∏ v, (cnt s v)!

lemma cnt_cons (a : Fin (m + 1)) (s : Fin L → Fin (m + 1)) (v : Fin (m + 1)) :
    cnt (Fin.cons a s) v = (if a = v then 1 else 0) + cnt s v := by
  unfold cnt
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- La suma de todas las multiplicidades es la longitud de la palabra. -/
lemma sum_cnt (s : Fin L → Fin (m + 1)) : ∑ v, cnt s v = L := by
  classical
  unfold cnt
  rw [Finset.sum_comm]
  have h1 : ∀ i : Fin L, (∑ v : Fin (m + 1), if s i = v then 1 else 0) = 1 := by
    intro i
    rw [Finset.sum_eq_single (s i) (fun b _ hb => if_neg fun h => hb h.symm)
      (fun h => absurd (Finset.mem_univ _) h)]
    exact if_pos rfl
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  simp

lemma sum_cnt_add_one (s : Fin L → Fin (m + 1)) :
    ∑ a, (cnt s a + 1) = L + (m + 1) := by
  rw [Finset.sum_add_distrib, sum_cnt]
  simp

/-- Añadir una letra `a` multiplica `∏_v a_v!` por `(a_a + 1)`. -/
lemma prod_cnt_cons (a : Fin (m + 1)) (s : Fin L → Fin (m + 1)) :
    (∏ v, (cnt (Fin.cons a s) v)!) = (cnt s a + 1) * ∏ v, (cnt s v)! := by
  classical
  rw [← Finset.mul_prod_erase univ (fun v => (cnt (Fin.cons a s) v)!) (Finset.mem_univ a),
      ← Finset.mul_prod_erase univ (fun v => (cnt s v)!) (Finset.mem_univ a)]
  have h2 : (∏ v ∈ univ.erase a, (cnt (Fin.cons a s) v)!)
      = ∏ v ∈ univ.erase a, (cnt s v)! := by
    refine Finset.prod_congr rfl fun v hv => ?_
    have hav : a ≠ v := fun h => (Finset.mem_erase.mp hv).1 h.symm
    simp [cnt_cons, hav]
  rw [h2, cnt_cons, if_pos rfl, add_comm 1 (cnt s a), Nat.factorial_succ]
  ring

/-- El paso clave: sumar sobre la letra añadida multiplica el peso por
`(L + m + 2)`.  Cálculo:
`∑_a (a₀+1+δ_{a,0})·(a_a+1) = (a₀+1)·(L+m+1) + (a₀+1) = (a₀+1)·(L+m+2)`. -/
lemma sum_wt_cons (s : Fin L → Fin (m + 1)) :
    ∑ a, wt (Fin.cons a s) = (L + m + 2) * wt s := by
  classical
  have hwt : ∀ a : Fin (m + 1), wt (Fin.cons a s)
      = (if a = 0 then 1 else 0) * ((cnt s a + 1) * ∏ v, (cnt s v)!)
        + (cnt s 0 + 1) * ((cnt s a + 1) * ∏ v, (cnt s v)!) := by
    intro a
    unfold wt
    rw [prod_cnt_cons, cnt_cons]
    ring
  rw [Finset.sum_congr rfl fun a _ => hwt a, Finset.sum_add_distrib]
  have hδ : (∑ a, (if a = 0 then 1 else 0) * ((cnt s a + 1) * ∏ v, (cnt s v)!))
      = (cnt s 0 + 1) * ∏ v, (cnt s v)! := by
    rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ 0) h)]
    simp
  have hmain : (∑ a, (cnt s 0 + 1) * ((cnt s a + 1) * ∏ v, (cnt s v)!))
      = (cnt s 0 + 1) * ((L + (m + 1)) * ∏ v, (cnt s v)!) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_cnt_add_one]
  rw [hδ, hmain]
  unfold wt
  ring

/-- Reindexación `(a, s) ↦ Fin.cons a s`. -/
def consEquiv (m L : ℕ) :
    (Fin (m + 1) × (Fin L → Fin (m + 1))) ≃ (Fin (L + 1) → Fin (m + 1)) where
  toFun p := Fin.cons p.1 p.2
  invFun s := (s 0, Fin.tail s)
  left_inv p := by simp
  right_inv s := Fin.cons_self_tail s

lemma sum_wt_zero (m : ℕ) : (∑ s : Fin 0 → Fin (m + 1), wt s) = 1 := by
  rw [Finset.sum_eq_single (fun i => i.elim0 : Fin 0 → Fin (m + 1))
    (fun b _ hb => absurd (funext fun i => i.elim0) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [wt, cnt]

/-- **Teorema principal (forma factorial exacta).**
`F(L) := ∑_{s : Fin L → Fin (m+1)} wt s` cumple `F(L+1) = (m+L+2)·F(L)`,
`F(0) = 1`, luego `F(L)·(m+1)! = (m+1+L)!`. -/
theorem sum_wt_mul_factorial (m L : ℕ) :
    (∑ s : Fin L → Fin (m + 1), wt s) * (m + 1)! = (m + 1 + L)! := by
  induction L with
  | zero =>
    rw [sum_wt_zero, one_mul, Nat.add_zero]
  | succ L ih =>
    have hsplit : (∑ s : Fin (L + 1) → Fin (m + 1), wt s)
        = (L + m + 2) * ∑ s : Fin L → Fin (m + 1), wt s := by
      calc (∑ s : Fin (L + 1) → Fin (m + 1), wt s)
          = ∑ p : Fin (m + 1) × (Fin L → Fin (m + 1)), wt (Fin.cons p.1 p.2) :=
            (Fintype.sum_equiv (consEquiv m L)
              (fun p => wt (Fin.cons p.1 p.2)) wt (fun p => rfl)).symm
        _ = ∑ a : Fin (m + 1), ∑ s : Fin L → Fin (m + 1), wt (Fin.cons a s) :=
            Fintype.sum_prod_type fun p => wt (Fin.cons p.1 p.2)
        _ = ∑ s : Fin L → Fin (m + 1), ∑ a : Fin (m + 1), wt (Fin.cons a s) :=
            Finset.sum_comm
        _ = ∑ s : Fin L → Fin (m + 1), (L + m + 2) * wt s :=
            Finset.sum_congr rfl fun s _ => sum_wt_cons s
        _ = (L + m + 2) * ∑ s : Fin L → Fin (m + 1), wt s :=
            (Finset.mul_sum _ _ _).symm
    rw [hsplit, mul_assoc, ih]
    have h1 : m + 1 + (L + 1) = (m + 1 + L) + 1 := by omega
    rw [h1, Nat.factorial_succ]
    congr 1
    omega

/-- Especialización Catalan: con `m = k+1` letras… es decir alfabeto
`Fin (k+2) = {0,…,k+1}` y longitud `L = k`, la suma vale `(k+1)! · C_{k+1}`. -/
theorem key (k : ℕ) :
    (∑ s : Fin k → Fin (k + 2), wt s) = (k + 1)! * catalan (k + 1) := by
  have h : (∑ s : Fin k → Fin (k + 2), wt s) * (k + 2)! = (2 * (k + 1))! := by
    have h0 := sum_wt_mul_factorial (k + 1) k
    have hidx : k + 1 + 1 + k = 2 * (k + 1) := by omega
    rw [hidx] at h0
    exact h0
  have h2 : (k + 1)! * catalan (k + 1) * (k + 2)! = (2 * (k + 1))! := by
    have hcb : (k + 1 + 1) * catalan (k + 1) = Nat.centralBinom (k + 1) :=
      succ_mul_catalan_eq_centralBinom (k + 1)
    have hcf := Nat.choose_mul_factorial_mul_factorial
      (show k + 1 ≤ 2 * (k + 1) by omega)
    have hsub : 2 * (k + 1) - (k + 1) = k + 1 := by omega
    rw [hsub] at hcf
    calc (k + 1)! * catalan (k + 1) * (k + 2)!
        = ((k + 1 + 1) * catalan (k + 1)) * ((k + 1)! * (k + 1)!) := by
          rw [show (k + 2)! = (k + 2) * (k + 1)! from Nat.factorial_succ (k + 1)]
          ring
      _ = Nat.centralBinom (k + 1) * ((k + 1)! * (k + 1)!) := by rw [hcb]
      _ = (2 * (k + 1)).choose (k + 1) * (k + 1)! * (k + 1)! := by
          simp only [Nat.centralBinom]
          ring
      _ = (2 * (k + 1))! := hcf
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k + 2)) (h.trans h2.symm)

/-- **Identidad de palabras, todo `n`** (resta truncada: `n = 0` da la palabra
vacía y `1 = 0!·C₀`).  Éste es el lado derecho del puente Prüfer. -/
theorem word_sum_eq (n : ℕ) :
    (∑ s : Fin (n - 1) → Fin (n + 1), wt s) = n ! * catalan n := by
  cases n with
  | zero => exact (sum_wt_zero 0).trans (by simp)
  | succ k => exact key k

/-- **Forma normalizada exacta**, imagen especular de
`rootedChildFactorialTreeSumNormalized`: una vez formalizado el puente Prüfer
(`treeSum n = wordSum n` en ℕ), esta igualdad produce
`RootedChildFactorialCatalanIdentity n` por composición directa. -/
theorem word_sum_normalized (n : ℕ) :
    ((n : ℝ) + 1) * (((n + 1)! : ℕ) : ℝ)⁻¹ *
      ((∑ s : Fin (n - 1) → Fin (n + 1), wt s : ℕ) : ℝ) = (catalan n : ℝ) := by
  have h := word_sum_eq n
  rw [h]
  have ha : ((n : ℝ) + 1) ≠ 0 := by
    have : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by rw [Nat.cast_add_one]
    rw [this]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hb : ((n ! : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  rw [Nat.cast_mul, hfact, mul_inv]
  calc ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * ((n ! : ℕ) : ℝ)⁻¹) *
        (((n ! : ℕ) : ℝ) * (catalan n : ℝ))
      = (((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹) * ((((n ! : ℕ) : ℝ))⁻¹ * ((n ! : ℕ) : ℝ))
          * (catalan n : ℝ) := by ring
    _ = 1 * 1 * (catalan n : ℝ) := by
        rw [mul_inv_cancel₀ ha, inv_mul_cancel₀ hb]
    _ = (catalan n : ℝ) := by ring

-- Comprobaciones finitas dentro del propio Lean (kernel, sin native_decide):
example : (∑ s : Fin 1 → Fin 3, wt s) = 4 := by decide
example : (∑ s : Fin 2 → Fin 4, wt s) = 30 := by decide

end RootedTreeCatalan

#print axioms RootedTreeCatalan.sum_wt_mul_factorial
#print axioms RootedTreeCatalan.word_sum_eq
#print axioms RootedTreeCatalan.word_sum_normalized
