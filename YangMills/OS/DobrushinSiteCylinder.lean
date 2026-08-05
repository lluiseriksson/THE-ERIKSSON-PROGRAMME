/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinInfiniteState

/-!
# Integer site cylinders and their algebraic direct limit

This module replaces centred-square presentations by an intrinsic carrier of
finite-site observables on `Z^2`.  A raw presentation consists of a finite set
of integer sites and a kernel on the spins at those sites.  Two presentations
are identified exactly when they define the same function on the full
configuration space.  The quotient therefore removes redundant sites and all
choices of finite support.

Pointwise constants, addition, multiplication, negation, and real scalar
multiplication descend to the quotient.  The full additive group `Z^2` acts by
translating the finite support; the action laws are proved after passage to the
quotient, where equality is extensional.  This file does not bundle the
operations into a `CommRing` or a normed/C-star structure.  No thermodynamic
limit or invariance property is assumed here.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical

/-- The additive lattice underlying the infinite two-dimensional model. -/
abbrev IsingSite := Fin 2 → ℤ

/-- A spin configuration on the full integer lattice. -/
abbrev InfiniteIsingConfig := IsingSite → Fin 2

/-- One finite-support presentation of a real cylinder observable. -/
structure SiteCylinderPresentation where
  support : Finset IsingSite
  kernel : (support → Fin 2) → ℝ

namespace SiteCylinderPresentation

/-- The global function represented by a finite cylinder presentation. -/
def realizeGlobal (O : SiteCylinderPresentation)
    (sigma : InfiniteIsingConfig) : ℝ :=
  O.kernel (fun s => sigma s.1)

/-- Constant presentation, carried by the empty support. -/
noncomputable def const (c : ℝ) : SiteCylinderPresentation where
  support := ∅
  kernel := fun _ => c

/-- Addition after passing both kernels to the union of their supports. -/
noncomputable def add (O P : SiteCylinderPresentation) :
    SiteCylinderPresentation where
  support := O.support ∪ P.support
  kernel := fun x =>
    O.kernel (fun s => x ⟨s.1, Finset.mem_union_left _ s.2⟩) +
      P.kernel (fun s => x ⟨s.1, Finset.mem_union_right _ s.2⟩)

/-- Pointwise multiplication after support enlargement. -/
noncomputable def mul (O P : SiteCylinderPresentation) :
    SiteCylinderPresentation where
  support := O.support ∪ P.support
  kernel := fun x =>
    O.kernel (fun s => x ⟨s.1, Finset.mem_union_left _ s.2⟩) *
      P.kernel (fun s => x ⟨s.1, Finset.mem_union_right _ s.2⟩)

/-- Additive inverse of a presentation. -/
def neg (O : SiteCylinderPresentation) : SiteCylinderPresentation where
  support := O.support
  kernel := fun x => -O.kernel x

/-- Real scalar multiplication of a presentation. -/
def smul (c : ℝ) (O : SiteCylinderPresentation) :
    SiteCylinderPresentation where
  support := O.support
  kernel := fun x => c * O.kernel x

@[simp] theorem realizeGlobal_const (c : ℝ) (sigma : InfiniteIsingConfig) :
    (const c).realizeGlobal sigma = c := rfl

@[simp] theorem realizeGlobal_add (O P : SiteCylinderPresentation)
    (sigma : InfiniteIsingConfig) :
    (add O P).realizeGlobal sigma =
      O.realizeGlobal sigma + P.realizeGlobal sigma := rfl

@[simp] theorem realizeGlobal_mul (O P : SiteCylinderPresentation)
    (sigma : InfiniteIsingConfig) :
    (mul O P).realizeGlobal sigma =
      O.realizeGlobal sigma * P.realizeGlobal sigma := rfl

@[simp] theorem realizeGlobal_neg (O : SiteCylinderPresentation)
    (sigma : InfiniteIsingConfig) :
    (neg O).realizeGlobal sigma = -O.realizeGlobal sigma := rfl

@[simp] theorem realizeGlobal_smul (c : ℝ) (O : SiteCylinderPresentation)
    (sigma : InfiniteIsingConfig) :
    (smul c O).realizeGlobal sigma = c * O.realizeGlobal sigma := rfl

/-- Translation of a presentation by an arbitrary integer vector. -/
noncomputable def translate (z : IsingSite) (O : SiteCylinderPresentation) :
    SiteCylinderPresentation where
  support := O.support.image (fun q => q + z)
  kernel := fun x => O.kernel (fun s =>
    x ⟨s.1 + z, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩)

@[simp] theorem realizeGlobal_translate (z : IsingSite)
    (O : SiteCylinderPresentation) (sigma : InfiniteIsingConfig) :
    (translate z O).realizeGlobal sigma =
      O.realizeGlobal (fun q => sigma (q + z)) := rfl

/-- Extensional equality of the represented global cylinder functions. -/
def Equivalent (O P : SiteCylinderPresentation) : Prop :=
  ∀ sigma, O.realizeGlobal sigma = P.realizeGlobal sigma

/-! ## Canonical centred charts -/

/-- Largest negative coordinate magnitude needed to place the support in a
centred square. -/
noncomputable def lowerRadius (O : SiteCylinderPresentation) : ℕ :=
  O.support.sup fun q =>
    (Finset.univ : Finset (Fin 2)).sup fun j => Int.toNat (-q j)

/-- Largest positive coordinate needed to place the support in a centred
square. -/
noncomputable def upperRadius (O : SiteCylinderPresentation) : ℕ :=
  O.support.sup fun q =>
    (Finset.univ : Finset (Fin 2)).sup fun j => Int.toNat (q j)

/-- Canonical centred radius of a presentation. -/
noncomputable def radius (O : SiteCylinderPresentation) : ℕ :=
  max O.lowerRadius O.upperRadius

theorem neg_coord_le_lowerRadius (O : SiteCylinderPresentation)
    (q : IsingSite) (hq : q ∈ O.support) (j : Fin 2) :
    -(q j) ≤ (O.lowerRadius : ℤ) := by
  have hj : Int.toNat (-q j) ≤
      (Finset.univ : Finset (Fin 2)).sup (fun k => Int.toNat (-q k)) :=
    Finset.le_sup (f := fun k : Fin 2 => Int.toNat (-q k))
      (Finset.mem_univ j)
  have hq' :
      (Finset.univ : Finset (Fin 2)).sup (fun k => Int.toNat (-q k)) ≤
        O.lowerRadius :=
    Finset.le_sup (f := fun q : IsingSite =>
      (Finset.univ : Finset (Fin 2)).sup fun k => Int.toNat (-q k)) hq
  by_cases hnonneg : 0 ≤ -(q j)
  · have hcast : ((Int.toNat (-q j) : ℕ) : ℤ) = -(q j) := by
      exact Int.toNat_of_nonneg hnonneg
    rw [← hcast]
    exact_mod_cast hj.trans hq'
  · have : 0 ≤ (O.lowerRadius : ℤ) := by omega
    omega

theorem coord_le_upperRadius (O : SiteCylinderPresentation)
    (q : IsingSite) (hq : q ∈ O.support) (j : Fin 2) :
    q j ≤ (O.upperRadius : ℤ) := by
  have hj : Int.toNat (q j) ≤
      (Finset.univ : Finset (Fin 2)).sup (fun k => Int.toNat (q k)) :=
    Finset.le_sup (f := fun k : Fin 2 => Int.toNat (q k))
      (Finset.mem_univ j)
  have hq' :
      (Finset.univ : Finset (Fin 2)).sup (fun k => Int.toNat (q k)) ≤
        O.upperRadius :=
    Finset.le_sup (f := fun q : IsingSite =>
      (Finset.univ : Finset (Fin 2)).sup fun k => Int.toNat (q k)) hq
  by_cases hnonneg : 0 ≤ q j
  · have hcast : ((Int.toNat (q j) : ℕ) : ℤ) = q j := by
      exact Int.toNat_of_nonneg hnonneg
    rw [← hcast]
    exact_mod_cast hj.trans hq'
  · have : 0 ≤ (O.upperRadius : ℤ) := by omega
    omega

theorem neg_radius_le_coord (O : SiteCylinderPresentation)
    (q : IsingSite) (hq : q ∈ O.support) (j : Fin 2) :
    -(O.radius : ℤ) ≤ q j := by
  have hlower := O.neg_coord_le_lowerRadius q hq j
  have hmax : O.lowerRadius ≤ O.radius := Nat.le_max_left _ _
  norm_num at hlower ⊢
  omega

theorem coord_le_radius (O : SiteCylinderPresentation)
    (q : IsingSite) (hq : q ∈ O.support) (j : Fin 2) :
    q j ≤ (O.radius : ℤ) := by
  have hupper := O.coord_le_upperRadius q hq j
  have hmax : O.upperRadius ≤ O.radius := Nat.le_max_right _ _
  norm_num at hupper ⊢
  omega

/-- A support coordinate in any sufficiently large centred chart. -/
noncomputable def siteAt (O : SiteCylinderPresentation) (R : ℕ)
    (hR : O.radius ≤ R) (q : O.support) : CenteredRect R :=
  (⟨Int.toNat (q.1 0 + (R : ℤ)), by
      have hlo := O.neg_radius_le_coord q.1 q.2 0
      have hhi := O.coord_le_radius q.1 q.2 0
      have hnonneg : 0 ≤ q.1 0 + (R : ℤ) := by omega
      have hcast := Int.toNat_of_nonneg hnonneg
      omega⟩,
   ⟨Int.toNat (q.1 1 + (R : ℤ)), by
      have hlo := O.neg_radius_le_coord q.1 q.2 1
      have hhi := O.coord_le_radius q.1 q.2 1
      have hnonneg : 0 ≤ q.1 1 + (R : ℤ) := by omega
      have hcast := Int.toNat_of_nonneg hnonneg
      omega⟩)

/-- Kernel of an integer presentation in a sufficiently large centred
square. -/
noncomputable def toCenteredKernelAt (O : SiteCylinderPresentation) (R : ℕ)
    (hR : O.radius ≤ R) : (CenteredRect R → Fin 2) → ℝ :=
  fun eta => O.kernel (fun q => eta (O.siteAt R hR q))

/-- Extend one centred spin configuration to the full lattice, using zero
outside the square. -/
noncomputable def extendCenteredConfig (R : ℕ)
    (eta : CenteredRect R → Fin 2) : InfiniteIsingConfig :=
  fun q =>
    if h0 : -(R : ℤ) ≤ q 0 ∧ q 0 ≤ (R : ℤ) then
      if h1 : -(R : ℤ) ≤ q 1 ∧ q 1 ≤ (R : ℤ) then
        eta
          (⟨Int.toNat (q 0 + (R : ℤ)), by
              have hn : 0 ≤ q 0 + (R : ℤ) := by omega
              have hcast := Int.toNat_of_nonneg hn
              omega⟩,
           ⟨Int.toNat (q 1 + (R : ℤ)), by
              have hn : 0 ≤ q 1 + (R : ℤ) := by omega
              have hcast := Int.toNat_of_nonneg hn
              omega⟩)
      else 0
    else 0

theorem toCenteredKernelAt_eq_realizeGlobal_extend
    (O : SiteCylinderPresentation) (R : ℕ) (hR : O.radius ≤ R)
    (eta : CenteredRect R → Fin 2) :
    O.toCenteredKernelAt R hR eta =
      O.realizeGlobal (extendCenteredConfig R eta) := by
  apply congrArg O.kernel
  funext q
  have hlo0 := O.neg_radius_le_coord q.1 q.2 0
  have hhi0 := O.coord_le_radius q.1 q.2 0
  have hlo1 := O.neg_radius_le_coord q.1 q.2 1
  have hhi1 := O.coord_le_radius q.1 q.2 1
  simp only [extendCenteredConfig]
  rw [dif_pos (by constructor <;> omega), dif_pos (by constructor <;> omega)]
  rfl

theorem toCenteredKernelAt_eq_of_equivalent
    (O P : SiteCylinderPresentation)
    (hOP : O.Equivalent P) (R : ℕ)
    (hO : O.radius ≤ R) (hP : P.radius ≤ R) :
    O.toCenteredKernelAt R hO = P.toCenteredKernelAt R hP := by
  funext eta
  rw [O.toCenteredKernelAt_eq_realizeGlobal_extend,
    P.toCenteredKernelAt_eq_realizeGlobal_extend]
  exact hOP _

/-- Enlarging the centred chart of an integer presentation agrees exactly
with the canonical centred lift. -/
theorem liftCenteredObservable_toCenteredKernelAt
    (O : SiteCylinderPresentation) {r R : ℕ}
    (hr : O.radius ≤ r) (hR : r ≤ R) :
    liftCenteredObservable hR (O.toCenteredKernelAt r hr) =
      O.toCenteredKernelAt R (hr.trans hR) := by
  funext eta
  unfold liftCenteredObservable toCenteredKernelAt
  apply congrArg O.kernel
  funext q
  apply congrArg eta
  change
    ((centeredRectEquiv hR (O.siteAt r hr q)).val) =
      O.siteAt R (hr.trans hR) q
  apply Prod.ext
  · apply Fin.ext
    change
      Int.toNat (q.1 0 + (r : ℤ)) + (R - r) =
        Int.toNat (q.1 0 + (R : ℤ))
    have hlo := O.neg_radius_le_coord q.1 q.2 0
    have hn0 : 0 ≤ q.1 0 + (r : ℤ) := by omega
    have hn1 : 0 ≤ q.1 0 + (R : ℤ) := by omega
    have hcast0 := Int.toNat_of_nonneg hn0
    have hcast1 := Int.toNat_of_nonneg hn1
    omega
  · apply Fin.ext
    change
      Int.toNat (q.1 1 + (r : ℤ)) + (R - r) =
        Int.toNat (q.1 1 + (R : ℤ))
    have hlo := O.neg_radius_le_coord q.1 q.2 1
    have hn0 : 0 ≤ q.1 1 + (r : ℤ) := by omega
    have hn1 : 0 ≤ q.1 1 + (R : ℤ) := by omega
    have hcast0 := Int.toNat_of_nonneg hn0
    have hcast1 := Int.toNat_of_nonneg hn1
    omega

instance : Setoid SiteCylinderPresentation where
  r := Equivalent
  iseqv :=
    ⟨fun _ _ => rfl,
      fun h sigma => (h sigma).symm,
      fun h k sigma => (h sigma).trans (k sigma)⟩

end SiteCylinderPresentation

/-- The algebraic local-cylinder carrier, implemented as the quotient by
equality of the induced global function. -/
def LocalCylinderAlgebra := Quotient SiteCylinderPresentation.instSetoid

namespace LocalCylinderAlgebra

/-- Quotient constructor. -/
def ofPresentation (O : SiteCylinderPresentation) : LocalCylinderAlgebra :=
  Quotient.mk' O

/-- The global realization is well-defined on the quotient. -/
def realizeGlobal (O : LocalCylinderAlgebra) : InfiniteIsingConfig → ℝ :=
  Quotient.lift SiteCylinderPresentation.realizeGlobal
    (fun _ _ h => funext h) O

theorem realizeGlobal_injective : Function.Injective realizeGlobal := by
  intro O P h
  induction O using Quotient.inductionOn with
  | _ O =>
      induction P using Quotient.inductionOn with
      | _ P =>
          apply Quotient.sound
          exact fun sigma => congrFun h sigma

/-- Constants in the quotient algebra. -/
noncomputable def const (c : ℝ) : LocalCylinderAlgebra :=
  ofPresentation (SiteCylinderPresentation.const c)

/-- Addition in the quotient algebra. -/
noncomputable def add (O P : LocalCylinderAlgebra) : LocalCylinderAlgebra :=
  Quotient.map₂ SiteCylinderPresentation.add
    (by
      intro O O' hO P P' hP sigma
      simp only [SiteCylinderPresentation.realizeGlobal_add]
      rw [hO sigma, hP sigma]) O P

/-- Multiplication in the quotient algebra. -/
noncomputable def mul (O P : LocalCylinderAlgebra) : LocalCylinderAlgebra :=
  Quotient.map₂ SiteCylinderPresentation.mul
    (by
      intro O O' hO P P' hP sigma
      simp only [SiteCylinderPresentation.realizeGlobal_mul]
      rw [hO sigma, hP sigma]) O P

/-- Additive inverse in the quotient algebra. -/
def neg (O : LocalCylinderAlgebra) : LocalCylinderAlgebra :=
  Quotient.map SiteCylinderPresentation.neg
    (by
      intro O P h sigma
      simp only [SiteCylinderPresentation.realizeGlobal_neg]
      rw [h sigma]) O

/-- Real scalar multiplication in the quotient algebra. -/
def smul (c : ℝ) (O : LocalCylinderAlgebra) : LocalCylinderAlgebra :=
  Quotient.map (SiteCylinderPresentation.smul c)
    (by
      intro O P h sigma
      simp only [SiteCylinderPresentation.realizeGlobal_smul]
      rw [h sigma]) O

noncomputable instance : Zero LocalCylinderAlgebra := ⟨const 0⟩
noncomputable instance : One LocalCylinderAlgebra := ⟨const 1⟩
noncomputable instance : Add LocalCylinderAlgebra := ⟨add⟩
noncomputable instance : Mul LocalCylinderAlgebra := ⟨mul⟩
instance : Neg LocalCylinderAlgebra := ⟨neg⟩
instance : SMul ℝ LocalCylinderAlgebra := ⟨smul⟩

@[simp] theorem realizeGlobal_zero : realizeGlobal (0 : LocalCylinderAlgebra) = 0 := rfl
@[simp] theorem realizeGlobal_one : realizeGlobal (1 : LocalCylinderAlgebra) = 1 := rfl
@[simp] theorem realizeGlobal_add (O P : LocalCylinderAlgebra) :
    realizeGlobal (O + P) = realizeGlobal O + realizeGlobal P := by
  apply funext
  induction O using Quotient.inductionOn with
  | _ O =>
      induction P using Quotient.inductionOn with
      | _ P => intro sigma; rfl

@[simp] theorem realizeGlobal_mul (O P : LocalCylinderAlgebra) :
    realizeGlobal (O * P) = realizeGlobal O * realizeGlobal P := by
  apply funext
  induction O using Quotient.inductionOn with
  | _ O =>
      induction P using Quotient.inductionOn with
      | _ P => intro sigma; rfl

@[simp] theorem realizeGlobal_neg (O : LocalCylinderAlgebra) :
    realizeGlobal (-O) = -realizeGlobal O := by
  apply funext
  induction O using Quotient.inductionOn with
  | _ O => intro sigma; rfl

@[simp] theorem realizeGlobal_smul (c : ℝ) (O : LocalCylinderAlgebra) :
    realizeGlobal (c • O) = c • realizeGlobal O := by
  apply funext
  induction O using Quotient.inductionOn with
  | _ O => intro sigma; rfl

/-- Translation on the quotient algebra. -/
noncomputable def translate (z : IsingSite) (O : LocalCylinderAlgebra) :
    LocalCylinderAlgebra :=
  Quotient.map (SiteCylinderPresentation.translate z)
    (by
      intro O P h sigma
      simp only [SiteCylinderPresentation.realizeGlobal_translate]
      exact h _) O

@[simp] theorem realizeGlobal_translate (z : IsingSite)
    (O : LocalCylinderAlgebra) :
    realizeGlobal (translate z O) =
      fun sigma => realizeGlobal O (fun q => sigma (q + z)) := by
  apply funext
  induction O using Quotient.inductionOn with
  | _ O => intro sigma; rfl

noncomputable instance : VAdd IsingSite LocalCylinderAlgebra :=
  ⟨translate⟩

@[simp] theorem zero_vadd (O : LocalCylinderAlgebra) :
    (0 : IsingSite) +ᵥ O = O := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (translate 0 O) sigma = realizeGlobal O sigma
  rw [realizeGlobal_translate]
  apply congrArg (realizeGlobal O)
  funext q
  simp

theorem add_vadd (z w : IsingSite) (O : LocalCylinderAlgebra) :
    (z + w) +ᵥ O = z +ᵥ (w +ᵥ O) := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (translate (z + w) O) sigma =
    realizeGlobal (translate z (translate w O)) sigma
  rw [realizeGlobal_translate, realizeGlobal_translate, realizeGlobal_translate]
  apply congrArg (realizeGlobal O)
  funext q
  simp [add_comm, add_left_comm]

noncomputable instance : AddAction IsingSite LocalCylinderAlgebra where
  zero_vadd := zero_vadd
  add_vadd := add_vadd

@[simp] theorem neg_vadd_vadd (z : IsingSite) (O : LocalCylinderAlgebra) :
    (-z) +ᵥ (z +ᵥ O) = O := by
  rw [← add_vadd]
  simp

theorem translate_add (z : IsingSite) (O P : LocalCylinderAlgebra) :
    z +ᵥ (O + P) = (z +ᵥ O) + (z +ᵥ P) := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (translate z (O + P)) sigma =
    realizeGlobal ((translate z O) + (translate z P)) sigma
  calc
    _ = realizeGlobal (O + P) (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_translate z (O + P)) sigma
    _ = realizeGlobal O (fun q => sigma (q + z)) +
        realizeGlobal P (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_add O P) _
    _ = realizeGlobal (translate z O) sigma +
        realizeGlobal (translate z P) sigma := by
      rw [congrFun (realizeGlobal_translate z O) sigma,
        congrFun (realizeGlobal_translate z P) sigma]
    _ = _ := (congrFun (realizeGlobal_add (translate z O) (translate z P)) sigma).symm

theorem translate_mul (z : IsingSite) (O P : LocalCylinderAlgebra) :
    z +ᵥ (O * P) = (z +ᵥ O) * (z +ᵥ P) := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (translate z (O * P)) sigma =
    realizeGlobal ((translate z O) * (translate z P)) sigma
  calc
    _ = realizeGlobal (O * P) (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_translate z (O * P)) sigma
    _ = realizeGlobal O (fun q => sigma (q + z)) *
        realizeGlobal P (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_mul O P) _
    _ = realizeGlobal (translate z O) sigma *
        realizeGlobal (translate z P) sigma := by
      rw [congrFun (realizeGlobal_translate z O) sigma,
        congrFun (realizeGlobal_translate z P) sigma]
    _ = _ := (congrFun (realizeGlobal_mul (translate z O) (translate z P)) sigma).symm

theorem translate_one (z : IsingSite) :
    z +ᵥ (1 : LocalCylinderAlgebra) = 1 := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (1 : LocalCylinderAlgebra) (fun q => sigma (q + z)) = 1
  exact congrFun realizeGlobal_one _

theorem translate_smul (z : IsingSite) (c : ℝ)
    (O : LocalCylinderAlgebra) :
    z +ᵥ (c • O) = c • (z +ᵥ O) := by
  apply realizeGlobal_injective
  funext sigma
  change realizeGlobal (translate z (c • O)) sigma =
    realizeGlobal (c • translate z O) sigma
  calc
    _ = realizeGlobal (c • O) (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_translate z (c • O)) sigma
    _ = c * realizeGlobal O (fun q => sigma (q + z)) :=
      congrFun (realizeGlobal_smul c O) _
    _ = c * realizeGlobal (translate z O) sigma := by
      rw [congrFun (realizeGlobal_translate z O) sigma]
    _ = _ := (congrFun (realizeGlobal_smul c (translate z O)) sigma).symm

end LocalCylinderAlgebra
end Dobrushin
end YangMills.OS
