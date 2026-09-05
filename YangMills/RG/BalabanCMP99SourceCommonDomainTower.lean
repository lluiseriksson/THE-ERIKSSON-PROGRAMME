/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceWeightedRegionalTower

/-!
# Every CMP99 source average from one common fine field

Printed CMP99 (3.18)--(3.19) uses a single fine field on `Omega_0` and the
prefixes

`Q'_0 = I`,  `Q'_{j+1} = Q_j Q'_j`.

The target Hilbert space changes with `j`.  A terminal-only tower therefore
does not by itself type the simultaneous sum in (3.24).  This file records
the complete dependent chain and constructs every prefix from the literal
one-step maps.  In particular, `Qprime` is not an arbitrary family supplied
after the fact.
-/

namespace YangMills.RG

noncomputable section

/-- A finite dependent chain of continuous linear maps.  The parameter
`Start` is the common domain of every prefix. -/
inductive CMP99SourceCommonDomainTower :
    CMP99SourceWeightedTowerHilbertSpace → ℕ → Type 2
  | stop (Start : CMP99SourceWeightedTowerHilbertSpace) :
      CMP99SourceCommonDomainTower Start 0
  | step {n : ℕ}
      (Start : CMP99SourceWeightedTowerHilbertSpace)
      (Next : CMP99SourceWeightedTowerHilbertSpace)
      (head : Start.carrier →L[ℝ] Next.carrier)
      (tail : CMP99SourceCommonDomainTower Next n) :
      CMP99SourceCommonDomainTower Start (n + 1)

namespace CMP99SourceCommonDomainTower

/-- Hilbert space at level `j`, including the common fine level `j = 0`. -/
def levelSpace
    {Start : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (T : CMP99SourceCommonDomainTower Start n) :
    Fin (n + 1) → CMP99SourceWeightedTowerHilbertSpace :=
  match n, T with
  | 0, .stop _ => fun _ => Start
  | _ + 1, .step _ _ _head tail =>
      fun j => Fin.cases Start (fun r => tail.levelSpace r) j

/-- The prefix `Q'_j : E_0 -> E_j`, constructed from the successive
one-scale maps in the printed order. -/
def Qprime
    {Start : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (T : CMP99SourceCommonDomainTower Start n) :
    ∀ j : Fin (n + 1), Start.carrier →L[ℝ] (T.levelSpace j).carrier :=
  match n, T with
  | 0, .stop _ => fun _ => ContinuousLinearMap.id ℝ Start.carrier
  | _ + 1, .step _ _ head tail =>
      fun j => Fin.cases
        (ContinuousLinearMap.id ℝ Start.carrier)
        (fun r => (tail.Qprime r).comp head) j

@[simp] theorem levelSpace_zero
    {Start : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (T : CMP99SourceCommonDomainTower Start n) :
    T.levelSpace 0 = Start := by
  cases T <;> rfl

/-- The zero prefix is the identity after the definitional level-space
identification. -/
theorem Qprime_zero
    {Start : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (T : CMP99SourceCommonDomainTower Start n) :
    HEq (T.Qprime 0) (ContinuousLinearMap.id ℝ Start.carrier) := by
  cases T <;> rfl

@[simp] theorem levelSpace_succ
    {Start Next : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (head : Start.carrier →L[ℝ] Next.carrier)
    (tail : CMP99SourceCommonDomainTower Next n) (r : Fin (n + 1)) :
    (CMP99SourceCommonDomainTower.step Start Next head tail).levelSpace r.succ =
      tail.levelSpace r := rfl

/-- Exact prefix recursion `Q'_{j+1} = Q_j Q'_j` for the dependent chain. -/
@[simp] theorem Qprime_succ
    {Start Next : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (head : Start.carrier →L[ℝ] Next.carrier)
    (tail : CMP99SourceCommonDomainTower Next n) (r : Fin (n + 1)) :
    (CMP99SourceCommonDomainTower.step Start Next head tail).Qprime r.succ =
      (tail.Qprime r).comp head := rfl

/-- The first nontrivial prefix is exactly the first one-scale map. -/
theorem Qprime_one
    {Start Next : CMP99SourceWeightedTowerHilbertSpace} {n : ℕ}
    (head : Start.carrier →L[ℝ] Next.carrier)
    (tail : CMP99SourceCommonDomainTower Next n) :
    HEq
      ((CMP99SourceCommonDomainTower.step Start Next head tail).Qprime
        (Fin.succ 0)) head := by
  rw [Qprime_succ]
  cases tail <;>
    exact heq_of_eq (ContinuousLinearMap.id_comp head)

end CMP99SourceCommonDomainTower

end

end YangMills.RG
