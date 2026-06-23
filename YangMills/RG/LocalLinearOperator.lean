/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.LocalFunctional
import YangMills.RG.ModifiedMetric

/-!
# Exact local linear-operator support on CMP116 fluctuation fields

This file defines the finite algebra needed to say that a linear operator on
CMP116 fluctuation coordinates exactly reads one cube set and exactly outputs
inside another.  The definition is by coordinate projections, not by an
exponential off-diagonal estimate or by a later Appendix-F activity bound.

The point is upstream of raw activity construction: a later source theorem can
decompose a nonlocal linear change of variables into pieces that are literally
supported between finite cube regions, then feed those pieces into a local
polymerization compiler.

Honest scope: this file proves only exact projection/support algebra for finite
CMP116 coordinate fields.  It does not construct physical fluctuation
activities, Gaussian change of variables, polymer decay, or any Appendix-F
cluster estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators

/-- CMP116 fluctuation coordinates, written as an ultralocal field over cubes. -/
abbrev CMP116FluctuationField (d L lieDim : ℕ) :=
  ∀ _ : Cube d L, Fin lieDim → ℝ

/-- Coordinate projection onto a finite set of CMP116 cubes. -/
noncomputable def cmp116FieldProjection
    {d L lieDim : ℕ} [NeZero L]
    (X : Finset (Cube d L)) :
    CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ q a => if q ∈ X then ξ q a else 0
      map_add' := fun ξ η => by
        funext q a
        by_cases hq : q ∈ X <;> simp [hq]
      map_smul' := fun c ξ => by
        funext q a
        by_cases hq : q ∈ X <;> simp [hq] }

@[simp] theorem cmp116FieldProjection_apply_mem
    {d L lieDim : ℕ} [NeZero L]
    (X : Finset (Cube d L)) {q : Cube d L} (hq : q ∈ X)
    (ξ : CMP116FluctuationField d L lieDim) (a : Fin lieDim) :
    cmp116FieldProjection X ξ q a = ξ q a := by
  simp [cmp116FieldProjection, hq]

@[simp] theorem cmp116FieldProjection_apply_not_mem
    {d L lieDim : ℕ} [NeZero L]
    (X : Finset (Cube d L)) {q : Cube d L} (hq : q ∉ X)
    (ξ : CMP116FluctuationField d L lieDim) (a : Fin lieDim) :
    cmp116FieldProjection X ξ q a = 0 := by
  simp [cmp116FieldProjection, hq]

@[simp] theorem cmp116FieldProjection_empty
    {d L lieDim : ℕ} [NeZero L] :
    cmp116FieldProjection (d := d) (L := L) (lieDim := lieDim) ∅ = 0 := by
  ext ξ q a
  simp [cmp116FieldProjection]

@[simp] theorem cmp116FieldProjection_univ
    {d L lieDim : ℕ} [NeZero L] :
    cmp116FieldProjection (d := d) (L := L) (lieDim := lieDim) Finset.univ =
      ContinuousLinearMap.id ℝ (CMP116FluctuationField d L lieDim) := by
  ext ξ q a
  simp [cmp116FieldProjection]

/-- Projection onto `X` after projection onto `Y` is projection onto the
intersection. -/
theorem cmp116FieldProjection_comp
    {d L lieDim : ℕ} [NeZero L]
    (X Y : Finset (Cube d L)) :
    (cmp116FieldProjection (lieDim := lieDim) X).comp
        (cmp116FieldProjection Y) =
      cmp116FieldProjection (lieDim := lieDim) (X ∩ Y) := by
  ext ξ q a
  by_cases hX : q ∈ X <;> by_cases hY : q ∈ Y <;>
    simp [cmp116FieldProjection, hX, hY]

/-- If `X ⊆ Y`, then projecting to `Y` before projecting to `X` changes
nothing. -/
theorem cmp116FieldProjection_comp_of_subset
    {d L lieDim : ℕ} [NeZero L]
    {X Y : Finset (Cube d L)} (hXY : X ⊆ Y) :
    (cmp116FieldProjection (lieDim := lieDim) X).comp
        (cmp116FieldProjection Y) =
      cmp116FieldProjection (lieDim := lieDim) X := by
  ext ξ q a
  by_cases hX : q ∈ X
  · have hY : q ∈ Y := hXY hX
    simp [cmp116FieldProjection, hX, hY]
  · by_cases hY : q ∈ Y <;> simp [cmp116FieldProjection, hX]

/-- If `X ⊆ Y`, then projecting to `Y` after projecting to `X` changes
nothing. -/
theorem cmp116FieldProjection_comp_of_subset_right
    {d L lieDim : ℕ} [NeZero L]
    {X Y : Finset (Cube d L)} (hXY : X ⊆ Y) :
    (cmp116FieldProjection (lieDim := lieDim) Y).comp
        (cmp116FieldProjection X) =
      cmp116FieldProjection (lieDim := lieDim) X := by
  ext ξ q a
  by_cases hX : q ∈ X
  · have hY : q ∈ Y := hXY hX
    simp [cmp116FieldProjection, hX, hY]
  · by_cases hY : q ∈ Y <;> simp [cmp116FieldProjection, hX]

/-- Projection preserves equality on the projected set. -/
theorem cmp116FieldProjection_eq_of_agreeOn
    {d L lieDim : ℕ} [NeZero L]
    {X : Finset (Cube d L)}
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn X ξ η) :
    cmp116FieldProjection (lieDim := lieDim) X ξ =
      cmp116FieldProjection X η := by
  funext q a
  by_cases hq : q ∈ X
  · simp [cmp116FieldProjection, hq, hξη q hq]
  · simp [cmp116FieldProjection, hq]

/-- Exact input/output support for a linear operator on CMP116 fluctuation
fields.  The first equality says the operator only reads `Xin`; the second says
its output vanishes outside `Xout`. -/
def OperatorSupportedBetween
    {d L lieDim : ℕ} [NeZero L]
    (Xin Xout : Finset (Cube d L))
    (T : CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim) : Prop :=
  T.comp (cmp116FieldProjection Xin) = T ∧
    (cmp116FieldProjection Xout).comp T = T

namespace OperatorSupportedBetween

variable {d L lieDim : ℕ} [NeZero L]
variable {Xin Xmid Xout Xin' Xout' : Finset (Cube d L)}
variable {T U : CMP116FluctuationField d L lieDim →L[ℝ]
  CMP116FluctuationField d L lieDim}

/-- The zero operator is supported between any two regions. -/
theorem zero :
    OperatorSupportedBetween Xin Xout
      (0 : CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim) := by
  constructor <;> ext ξ q a <;> simp

/-- An input-supported operator gives the same value on fields agreeing on the
input region. -/
theorem eq_of_agreeOn
    (hT : OperatorSupportedBetween Xin Xout T)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    T ξ = T η := by
  have hξ := congrArg (fun S => S ξ) hT.1
  have hη := congrArg (fun S => S η) hT.1
  calc
    T ξ = T (cmp116FieldProjection Xin ξ) := by
      simpa [ContinuousLinearMap.comp_apply] using hξ.symm
    _ = T (cmp116FieldProjection Xin η) := by
      rw [cmp116FieldProjection_eq_of_agreeOn hξη]
    _ = T η := by
      simpa [ContinuousLinearMap.comp_apply] using hη

/-- An output-supported operator is pointwise zero outside the output region. -/
theorem apply_eq_zero_outside
    (hT : OperatorSupportedBetween Xin Xout T)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    T ξ q a = 0 := by
  have hout := congrArg (fun S => S ξ) hT.2
  have hcoord := congrFun (congrFun hout q) a
  simpa [ContinuousLinearMap.comp_apply, cmp116FieldProjection, hq] using
    hcoord.symm

/-- Exact support is closed under addition when the supports are the same. -/
theorem add
    (hT : OperatorSupportedBetween Xin Xout T)
    (hU : OperatorSupportedBetween Xin Xout U) :
    OperatorSupportedBetween Xin Xout (T + U) := by
  constructor
  · ext ξ q a
    have hTξ := congrArg (fun S => S ξ) hT.1
    have hUξ := congrArg (fun S => S ξ) hU.1
    simp [hTξ, hUξ]
  · ext ξ q a
    have hTξ := congrArg (fun S => S ξ) hT.2
    have hUξ := congrArg (fun S => S ξ) hU.2
    simp [hTξ, hUξ]

/-- Exact support is closed under finite sums when the supports are the same. -/
theorem finsetSum {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (A : ι → CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim)
    (hA : ∀ i, i ∈ I → OperatorSupportedBetween Xin Xout (A i)) :
    OperatorSupportedBetween Xin Xout (I.sum A) := by
  classical
  revert hA
  refine Finset.induction_on I ?base ?step
  · intro _hA
    simpa using (zero (d := d) (L := L) (lieDim := lieDim)
      (Xin := Xin) (Xout := Xout))
  · intro i I hi hI hA
    have hiA : OperatorSupportedBetween Xin Xout (A i) :=
      hA i (Finset.mem_insert_self i I)
    have hrest : OperatorSupportedBetween Xin Xout (I.sum A) :=
      hI (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using add hiA hrest

/-- Exact support composes: if `T` outputs in the input region of `U`, then
`U.comp T` reads where `T` reads and outputs where `U` outputs. -/
theorem comp
    (hT : OperatorSupportedBetween Xin Xmid T)
    (hU : OperatorSupportedBetween Xmid Xout U) :
    OperatorSupportedBetween Xin Xout (U.comp T) := by
  constructor
  · ext ξ q a
    have hTin := congrArg (fun S => S ξ) hT.1
    simp [ContinuousLinearMap.comp_apply] at hTin ⊢
    rw [hTin]
  · ext ξ q a
    have hUout := congrArg (fun S => S (T ξ)) hU.2
    simpa [ContinuousLinearMap.comp_apply] using
      congrFun (congrFun hUout q) a

/-- Exact support is monotone under enlarging input and output regions. -/
theorem mono
    (hTin : Xin ⊆ Xin') (hTout : Xout ⊆ Xout')
    (hT : OperatorSupportedBetween Xin Xout T) :
    OperatorSupportedBetween Xin' Xout' T := by
  constructor
  · calc
      T.comp (cmp116FieldProjection Xin') =
          (T.comp (cmp116FieldProjection Xin)).comp
            (cmp116FieldProjection Xin') := by
        rw [hT.1]
      _ = T.comp ((cmp116FieldProjection Xin).comp
            (cmp116FieldProjection Xin')) := rfl
      _ = T.comp (cmp116FieldProjection Xin) := by
        rw [cmp116FieldProjection_comp_of_subset hTin]
      _ = T := hT.1
  · calc
      (cmp116FieldProjection Xout').comp T =
          (cmp116FieldProjection Xout').comp
            ((cmp116FieldProjection Xout).comp T) := by
        rw [hT.2]
      _ = ((cmp116FieldProjection Xout').comp
            (cmp116FieldProjection Xout)).comp T := rfl
      _ = (cmp116FieldProjection Xout).comp T := by
        rw [cmp116FieldProjection_comp_of_subset_right hTout]
      _ = T := hT.2

end OperatorSupportedBetween

end YangMills.RG
