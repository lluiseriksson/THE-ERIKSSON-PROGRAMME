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

/-- A CMP116 field concentrated at one cube.  The vector `v` contains all local
fluctuation coordinates at that cube. -/
def singleCMP116CubeField
    {d L lieDim : ℕ} [NeZero L]
    (source : Cube d L) (v : Fin lieDim → ℝ) :
    CMP116FluctuationField d L lieDim :=
  fun target a => if target = source then v a else 0

@[simp] theorem singleCMP116CubeField_self
    {d L lieDim : ℕ} [NeZero L]
    (source : Cube d L) (v : Fin lieDim → ℝ) :
    singleCMP116CubeField source v source = v := by
  funext a
  simp [singleCMP116CubeField]

@[simp] theorem singleCMP116CubeField_of_ne
    {d L lieDim : ℕ} [NeZero L]
    {source target : Cube d L} (h : target ≠ source)
    (v : Fin lieDim → ℝ) :
    singleCMP116CubeField source v target = 0 := by
  funext a
  simp [singleCMP116CubeField, h]

@[simp] theorem singleCMP116CubeField_zero
    {d L lieDim : ℕ} [NeZero L]
    (source : Cube d L) :
    singleCMP116CubeField source (0 : Fin lieDim → ℝ) = 0 := by
  funext target a
  simp [singleCMP116CubeField]

/-- Every finite CMP116 field is the sum of its single-cube fields. -/
theorem cmp116Field_eq_sum_singleCube
    {d L lieDim : ℕ} [NeZero L]
    (ξ : CMP116FluctuationField d L lieDim) :
    ξ =
      ∑ source : Cube d L,
        singleCMP116CubeField source (ξ source) := by
  classical
  funext target a
  simp [singleCMP116CubeField]

/-- A continuous linear map is determined on a finite CMP116 field by the sum
of its values on the single-cube pieces. -/
theorem map_cmp116Field_eq_sum_singleCube
    {d L lieDim : ℕ} [NeZero L]
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim) :
    T ξ =
      ∑ source : Cube d L,
        T (singleCMP116CubeField source (ξ source)) := by
  calc
    T ξ =
        T (∑ source : Cube d L,
          singleCMP116CubeField source (ξ source)) := by
      exact congrArg T (cmp116Field_eq_sum_singleCube ξ)
    _ = ∑ source : Cube d L,
          T (singleCMP116CubeField source (ξ source)) := by
      simp

/-- If a continuous linear map vanishes on every single-cube component of a
field, then it vanishes on the field. -/
theorem map_cmp116Field_eq_zero_of_singleCube_eq_zero
    {d L lieDim : ℕ} [NeZero L]
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim)
    (hzero :
      ∀ source : Cube d L,
        T (singleCMP116CubeField source (ξ source)) = 0) :
    T ξ = 0 := by
  classical
  rw [map_cmp116Field_eq_sum_singleCube T ξ]
  apply Finset.sum_eq_zero
  intro source _hsource
  exact hzero source

@[simp] theorem cmp116FieldProjection_single_mem
    {d L lieDim : ℕ} [NeZero L]
    (X : Finset (Cube d L)) {source : Cube d L}
    (hsource : source ∈ X) (v : Fin lieDim → ℝ) :
    cmp116FieldProjection X (singleCMP116CubeField source v) =
      singleCMP116CubeField source v := by
  funext target a
  by_cases htarget : target = source
  · subst target
    simp [cmp116FieldProjection, hsource]
  · simp [cmp116FieldProjection, singleCMP116CubeField, htarget]

@[simp] theorem cmp116FieldProjection_single_not_mem
    {d L lieDim : ℕ} [NeZero L]
    (X : Finset (Cube d L)) {source : Cube d L}
    (hsource : source ∉ X) (v : Fin lieDim → ℝ) :
    cmp116FieldProjection X (singleCMP116CubeField source v) = 0 := by
  funext target a
  by_cases htarget : target = source
  · subst target
    simp [cmp116FieldProjection, hsource]
  · simp [cmp116FieldProjection, singleCMP116CubeField, htarget]

/-- Pointwise kernel bound for a linear map on CMP116 cube fields. -/
def CMP116LinearMapKernelBound
    {d L lieDim : ℕ} [NeZero L]
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    (weight : Cube d L → Cube d L → ℝ) : Prop :=
  ∀ source target (v : Fin lieDim → ℝ),
    ‖T (singleCMP116CubeField source v) target‖ ≤
      weight target source * ‖v‖

/-- Exact finite range of a CMP116 kernel weight. -/
def CMP116KernelFiniteRange
    {d L : ℕ} [NeZero L]
    (weight : Cube d L → Cube d L → ℝ)
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ) : Prop :=
  ∀ source target,
    R < dist target source →
      weight target source = 0

/-- The `R`-range enlargement of an input cube set. -/
noncomputable def cmp116FiniteRangeClosure
    {d L : ℕ} [NeZero L]
    (dist : Cube d L → Cube d L → ℕ)
    (R : ℕ) (X : Finset (Cube d L)) :
    Finset (Cube d L) := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ X, dist target source ≤ R

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

/-- It suffices to verify exact kernel zeros on single-cube fields. -/
theorem of_singleBond_kernel_zero
    {Xin Xout : Finset (Cube d L)}
    {T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim}
    (hzero :
      ∀ source target (v : Fin lieDim → ℝ),
        source ∉ Xin ∨ target ∉ Xout →
          T (singleCMP116CubeField source v) target = 0) :
    OperatorSupportedBetween Xin Xout T := by
  classical
  constructor
  · ext ξ target a
    have hdiff :
        T (ξ - cmp116FieldProjection Xin ξ) = 0 := by
      apply map_cmp116Field_eq_zero_of_singleCube_eq_zero
      intro source
      by_cases hsourceXin : source ∈ Xin
      · have hsourceZero :
            (ξ - cmp116FieldProjection Xin ξ) source = 0 := by
          funext b
          simp [cmp116FieldProjection, hsourceXin]
        simp [hsourceZero]
      · funext target b
        have hkernelZero :
            T (singleCMP116CubeField source
              ((ξ - cmp116FieldProjection Xin ξ) source)) target = 0 :=
          hzero source target
            ((ξ - cmp116FieldProjection Xin ξ) source) (Or.inl hsourceXin)
        exact congrFun hkernelZero b
    have hsub :
        T ξ - T (cmp116FieldProjection Xin ξ) = 0 := by
      simpa [map_sub] using hdiff
    have heq :
        T (cmp116FieldProjection Xin ξ) = T ξ :=
      (sub_eq_zero.mp hsub).symm
    exact congrFun (congrFun heq target) a
  · ext ξ target a
    by_cases htarget : target ∈ Xout
    · simp [ContinuousLinearMap.comp_apply, cmp116FieldProjection, htarget]
    · have hfull :
          T ξ target a =
            (∑ source : Cube d L,
              T (singleCMP116CubeField source (ξ source)) target a) := by
        simpa using
          congrFun (congrFun
            (map_cmp116Field_eq_sum_singleCube T ξ) target) a
      have hzero_sum :
          (∑ source : Cube d L,
            T (singleCMP116CubeField source (ξ source)) target a) = 0 := by
        apply Finset.sum_eq_zero
        intro source _hsource
        have hkernelZero :
            T (singleCMP116CubeField source (ξ source)) target = 0 :=
          hzero source target (ξ source) (Or.inr htarget)
        exact congrFun hkernelZero a
      have hTzero : T ξ target a = 0 := by
        rw [hfull, hzero_sum]
      rw [ContinuousLinearMap.comp_apply]
      simp [cmp116FieldProjection, htarget, hTzero]

/-- A kernel bound with exact finite range gives exact support after projecting
the input to `Xin`. -/
theorem of_kernel_bound_finiteRange
    {Xin : Finset (Cube d L)}
    {T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim}
    {weight : Cube d L → Cube d L → ℝ}
    {dist : Cube d L → Cube d L → ℕ}
    {R : ℕ}
    (hkernel : CMP116LinearMapKernelBound T weight)
    (hrange : CMP116KernelFiniteRange weight dist R) :
    OperatorSupportedBetween
      Xin
      (cmp116FiniteRangeClosure dist R Xin)
      (T.comp (cmp116FieldProjection Xin)) := by
  classical
  apply of_singleBond_kernel_zero
  intro source target v houtside
  rcases houtside with hsource | htarget
  · simp [ContinuousLinearMap.comp_apply, hsource]
  · by_cases hsourceXin : source ∈ Xin
    · have hnotDistLe : ¬ dist target source ≤ R := by
        intro hdistLe
        have hmem : target ∈ cmp116FiniteRangeClosure dist R Xin := by
          simp [cmp116FiniteRangeClosure]
          exact ⟨source, hsourceXin, hdistLe⟩
        exact htarget hmem
      have hdist : R < dist target source := Nat.lt_of_not_ge hnotDistLe
      have hweight : weight target source = 0 := hrange source target hdist
      have hbound := hkernel source target v
      have hnorm_le_zero :
          ‖T (singleCMP116CubeField source v) target‖ ≤ 0 := by
        simpa [hweight] using hbound
      have hnorm_eq_zero :
          ‖T (singleCMP116CubeField source v) target‖ = 0 :=
        le_antisymm hnorm_le_zero (norm_nonneg _)
      have hkernelZero :
          T (singleCMP116CubeField source v) target = 0 :=
        norm_eq_zero.mp hnorm_eq_zero
      simp [ContinuousLinearMap.comp_apply, hsourceXin, hkernelZero]
    · simp [ContinuousLinearMap.comp_apply, hsourceXin]

end OperatorSupportedBetween

/-- A continuous linear map carrying certified exact input/output support. -/
structure CMP116LocalizedLinearMap
    {d L lieDim : ℕ} [NeZero L]
    (Xin Xout : Finset (Cube d L)) where
  toContinuousLinearMap :
    CMP116FluctuationField d L lieDim →L[ℝ]
      CMP116FluctuationField d L lieDim
  supportedBetween :
    OperatorSupportedBetween Xin Xout toContinuousLinearMap

namespace CMP116LocalizedLinearMap

variable {d L lieDim : ℕ} [NeZero L]
variable {Xin Xmid Xout : Finset (Cube d L)}

theorem eq_of_agreeOn
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    T.toContinuousLinearMap ξ =
      T.toContinuousLinearMap η :=
  OperatorSupportedBetween.eq_of_agreeOn
    T.supportedBetween hξη

theorem apply_eq_zero_outside
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    T.toContinuousLinearMap ξ q a = 0 :=
  OperatorSupportedBetween.apply_eq_zero_outside
    T.supportedBetween ξ hq a

noncomputable def add
    (T U : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout) :
    CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout where
  toContinuousLinearMap :=
    T.toContinuousLinearMap + U.toContinuousLinearMap
  supportedBetween :=
    OperatorSupportedBetween.add
      T.supportedBetween U.supportedBetween

@[simp] theorem add_toContinuousLinearMap
    (T U : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout) :
    (T.add U).toContinuousLinearMap =
      T.toContinuousLinearMap + U.toContinuousLinearMap :=
  rfl

/-- Addition preserves the declared input-agreement consequence. -/
theorem add_eq_of_agreeOn
    (T U : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    (T.add U).toContinuousLinearMap ξ =
      (T.add U).toContinuousLinearMap η :=
  (T.add U).eq_of_agreeOn hξη

/-- Addition preserves the declared output-zero consequence. -/
theorem add_apply_eq_zero_outside
    (T U : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    (T.add U).toContinuousLinearMap ξ q a = 0 :=
  (T.add U).apply_eq_zero_outside ξ hq a

noncomputable def finsetSum
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (T : ι → CMP116LocalizedLinearMap
      (lieDim := lieDim) Xin Xout) :
    CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout where
  toContinuousLinearMap :=
    I.sum fun i => (T i).toContinuousLinearMap
  supportedBetween :=
    OperatorSupportedBetween.finsetSum
      I
      (fun i => (T i).toContinuousLinearMap)
      (fun i _hi => (T i).supportedBetween)

@[simp] theorem finsetSum_toContinuousLinearMap
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (T : ι → CMP116LocalizedLinearMap
      (lieDim := lieDim) Xin Xout) :
    (finsetSum I T).toContinuousLinearMap =
      I.sum fun i => (T i).toContinuousLinearMap :=
  rfl

/-- Finite sums preserve the declared input-agreement consequence. -/
theorem finsetSum_eq_of_agreeOn
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (T : ι → CMP116LocalizedLinearMap
      (lieDim := lieDim) Xin Xout)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    (finsetSum I T).toContinuousLinearMap ξ =
      (finsetSum I T).toContinuousLinearMap η :=
  (finsetSum I T).eq_of_agreeOn hξη

/-- Finite sums preserve the declared output-zero consequence. -/
theorem finsetSum_apply_eq_zero_outside
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (T : ι → CMP116LocalizedLinearMap
      (lieDim := lieDim) Xin Xout)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    (finsetSum I T).toContinuousLinearMap ξ q a = 0 :=
  (finsetSum I T).apply_eq_zero_outside ξ hq a

/-- Finite sum of localized maps with varying input/output supports, supported
on the finite unions of the declared supports.  This is exact support algebra,
not a finite-range or decay estimate. -/
noncomputable def finsetSumVarying
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (Xin Xout : ι → Finset (Cube d L))
    (T : ∀ i, CMP116LocalizedLinearMap
      (lieDim := lieDim) (Xin i) (Xout i)) :
    CMP116LocalizedLinearMap
      (lieDim := lieDim) (I.biUnion Xin) (I.biUnion Xout) where
  toContinuousLinearMap :=
    I.sum fun i => (T i).toContinuousLinearMap
  supportedBetween := by
    classical
    refine OperatorSupportedBetween.finsetSum I
      (fun i => (T i).toContinuousLinearMap) ?_
    intro i hi
    exact
      OperatorSupportedBetween.mono
        (by
          intro q hq
          exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩)
        (by
          intro q hq
          exact Finset.mem_biUnion.mpr ⟨i, hi, hq⟩)
        (T i).supportedBetween

@[simp] theorem finsetSumVarying_toContinuousLinearMap
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (Xin Xout : ι → Finset (Cube d L))
    (T : ∀ i, CMP116LocalizedLinearMap
      (lieDim := lieDim) (Xin i) (Xout i)) :
    (finsetSumVarying I Xin Xout T).toContinuousLinearMap =
      I.sum fun i => (T i).toContinuousLinearMap :=
  rfl

/-- A varying-support finite sum depends only on the union of its declared
input supports. -/
theorem finsetSumVarying_eq_of_agreeOn
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (Xin Xout : ι → Finset (Cube d L))
    (T : ∀ i, CMP116LocalizedLinearMap
      (lieDim := lieDim) (Xin i) (Xout i))
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn (I.biUnion Xin) ξ η) :
    (finsetSumVarying I Xin Xout T).toContinuousLinearMap ξ =
      (finsetSumVarying I Xin Xout T).toContinuousLinearMap η :=
  (finsetSumVarying I Xin Xout T).eq_of_agreeOn hξη

/-- A varying-support finite sum is zero outside the union of its declared
output supports. -/
theorem finsetSumVarying_apply_eq_zero_outside
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (Xin Xout : ι → Finset (Cube d L))
    (T : ∀ i, CMP116LocalizedLinearMap
      (lieDim := lieDim) (Xin i) (Xout i))
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ I.biUnion Xout) (a : Fin lieDim) :
    (finsetSumVarying I Xin Xout T).toContinuousLinearMap ξ q a = 0 :=
  (finsetSumVarying I Xin Xout T).apply_eq_zero_outside ξ hq a

noncomputable def comp
    (U : CMP116LocalizedLinearMap (lieDim := lieDim) Xmid Xout)
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xmid) :
    CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout where
  toContinuousLinearMap :=
    U.toContinuousLinearMap.comp T.toContinuousLinearMap
  supportedBetween :=
    OperatorSupportedBetween.comp
      T.supportedBetween U.supportedBetween

@[simp] theorem comp_toContinuousLinearMap
    (U : CMP116LocalizedLinearMap (lieDim := lieDim) Xmid Xout)
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xmid) :
    (U.comp T).toContinuousLinearMap =
      U.toContinuousLinearMap.comp T.toContinuousLinearMap :=
  rfl

/-- Composition preserves the declared input-agreement consequence. -/
theorem comp_eq_of_agreeOn
    (U : CMP116LocalizedLinearMap (lieDim := lieDim) Xmid Xout)
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xmid)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    (U.comp T).toContinuousLinearMap ξ =
      (U.comp T).toContinuousLinearMap η :=
  (U.comp T).eq_of_agreeOn hξη

/-- Composition preserves the declared output-zero consequence. -/
theorem comp_apply_eq_zero_outside
    (U : CMP116LocalizedLinearMap (lieDim := lieDim) Xmid Xout)
    (T : CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xmid)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    (U.comp T).toContinuousLinearMap ξ q a = 0 :=
  (U.comp T).apply_eq_zero_outside ξ hq a

/-- Exact localization by input/output projection, with no decay claim. -/
noncomputable def ofProjection
    (Xin Xout : Finset (Cube d L))
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim) :
    CMP116LocalizedLinearMap (lieDim := lieDim) Xin Xout where
  toContinuousLinearMap :=
    (cmp116FieldProjection Xout).comp
      (T.comp (cmp116FieldProjection Xin))
  supportedBetween := by
    apply OperatorSupportedBetween.of_singleBond_kernel_zero
    intro source target v houtside
    rcases houtside with hsource | htarget
    · simp [ContinuousLinearMap.comp_apply, hsource]
    · funext a
      simp [ContinuousLinearMap.comp_apply, cmp116FieldProjection, htarget]

@[simp] theorem ofProjection_toContinuousLinearMap
    (Xin Xout : Finset (Cube d L))
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim) :
    (ofProjection (lieDim := lieDim) Xin Xout T).toContinuousLinearMap =
      (cmp116FieldProjection Xout).comp
        (T.comp (cmp116FieldProjection Xin)) :=
  rfl

/-- Projected localization exposes the declared input-agreement consequence. -/
theorem ofProjection_eq_of_agreeOn
    (Xin Xout : Finset (Cube d L))
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    {ξ η : CMP116FluctuationField d L lieDim}
    (hξη : AgreeOn Xin ξ η) :
    (ofProjection (lieDim := lieDim) Xin Xout T).toContinuousLinearMap ξ =
      (ofProjection (lieDim := lieDim) Xin Xout T).toContinuousLinearMap η :=
  (ofProjection (lieDim := lieDim) Xin Xout T).eq_of_agreeOn hξη

/-- Projected localization exposes the declared output-zero consequence. -/
theorem ofProjection_apply_eq_zero_outside
    (Xin Xout : Finset (Cube d L))
    (T :
      CMP116FluctuationField d L lieDim →L[ℝ]
        CMP116FluctuationField d L lieDim)
    (ξ : CMP116FluctuationField d L lieDim)
    {q : Cube d L} (hq : q ∉ Xout) (a : Fin lieDim) :
    (ofProjection (lieDim := lieDim) Xin Xout T).toContinuousLinearMap ξ q a =
      0 :=
  (ofProjection (lieDim := lieDim) Xin Xout T).apply_eq_zero_outside ξ hq a

end CMP116LocalizedLinearMap

end YangMills.RG
