/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinUniformState
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.UniformSpace.Separation

/-!
# The quasilocal commutative C-star algebra and the extended Dobrushin state

Real local cylinders are complexified explicitly, represented faithfully as
bounded continuous functions on the full product configuration space, and
completed by taking the uniform closure of their image.  The contractive real
state is complexified, extended uniquely from the dense local subalgebra, and
shown positive on the closure.

The construction remains inside the visible anisotropic Dobrushin window.  No
DLR equation and no claim beyond that window is made in this module.
-/

namespace YangMills.OS
namespace Dobrushin

open Classical Set
open scoped BoundedContinuousFunction ComplexOrder

/-! ## Continuity of finite-support cylinders -/

theorem SiteCylinderPresentation.continuous_realizeGlobal
    (O : SiteCylinderPresentation) : Continuous O.realizeGlobal := by
  unfold SiteCylinderPresentation.realizeGlobal
  apply continuous_of_discreteTopology.comp
  exact continuous_pi fun s => continuous_apply s.1

theorem LocalCylinderAlgebra.continuous_realizeGlobal
    (O : LocalCylinderAlgebra) : Continuous O.realizeGlobal := by
  induction O using Quotient.inductionOn with
  | _ O => exact O.continuous_realizeGlobal

/-! ## Explicit complexification -/

/-- A complex local cylinder is a real and an imaginary local cylinder. -/
structure ComplexLocalCylinderAlgebra where
  re : LocalCylinderAlgebra
  im : LocalCylinderAlgebra

namespace ComplexLocalCylinderAlgebra

/-- Global complex realization. -/
noncomputable def realizeGlobal (O : ComplexLocalCylinderAlgebra) :
    InfiniteIsingConfig → ℂ :=
  fun sigma => O.re.realizeGlobal sigma + Complex.I * O.im.realizeGlobal sigma

theorem realizeGlobal_injective : Function.Injective realizeGlobal := by
  intro O P h
  cases O with
  | mk Ore Oim =>
      cases P with
      | mk Pre Pim =>
          congr
          · apply LocalCylinderAlgebra.realizeGlobal_injective
            funext sigma
            have hs := congrArg Complex.re (congrFun h sigma)
            simpa [realizeGlobal] using hs
          · apply LocalCylinderAlgebra.realizeGlobal_injective
            funext sigma
            have hs := congrArg Complex.im (congrFun h sigma)
            simpa [realizeGlobal] using hs

noncomputable instance : Zero ComplexLocalCylinderAlgebra :=
  ⟨0, 0⟩

noncomputable instance : One ComplexLocalCylinderAlgebra :=
  ⟨1, 0⟩

noncomputable instance : Add ComplexLocalCylinderAlgebra :=
  ⟨fun O P => ⟨O.re + P.re, O.im + P.im⟩⟩

noncomputable instance : Mul ComplexLocalCylinderAlgebra :=
  ⟨fun O P => ⟨O.re * P.re - O.im * P.im,
    O.re * P.im + O.im * P.re⟩⟩

noncomputable instance : Neg ComplexLocalCylinderAlgebra :=
  ⟨fun O => ⟨-O.re, -O.im⟩⟩

noncomputable instance : Sub ComplexLocalCylinderAlgebra :=
  ⟨fun O P => O + -P⟩

noncomputable instance : SMul ℂ ComplexLocalCylinderAlgebra :=
  ⟨fun c O => ⟨c.re • O.re - c.im • O.im,
    c.re • O.im + c.im • O.re⟩⟩

noncomputable instance : Pow ComplexLocalCylinderAlgebra ℕ :=
  ⟨fun O n => Nat.rec 1 (fun _ P => P * O) n⟩

noncomputable instance : NatCast ComplexLocalCylinderAlgebra :=
  ⟨fun n => ⟨n, 0⟩⟩

noncomputable instance : IntCast ComplexLocalCylinderAlgebra :=
  ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem add_re (O P : ComplexLocalCylinderAlgebra) :
    (O + P).re = O.re + P.re := rfl

@[simp] theorem add_im (O P : ComplexLocalCylinderAlgebra) :
    (O + P).im = O.im + P.im := rfl

@[simp] theorem mul_re (O P : ComplexLocalCylinderAlgebra) :
    (O * P).re = O.re * P.re - O.im * P.im := rfl

@[simp] theorem mul_im (O P : ComplexLocalCylinderAlgebra) :
    (O * P).im = O.re * P.im + O.im * P.re := rfl

@[simp] theorem smul_re (c : ℂ) (O : ComplexLocalCylinderAlgebra) :
    (c • O).re = c.re • O.re - c.im • O.im := rfl

@[simp] theorem smul_im (c : ℂ) (O : ComplexLocalCylinderAlgebra) :
    (c • O).im = c.re • O.im + c.im • O.re := rfl

@[simp] theorem realizeGlobal_zero : realizeGlobal 0 = 0 := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal 0 sigma : ℝ) : ℂ) +
    Complex.I * (LocalCylinderAlgebra.realizeGlobal 0 sigma : ℝ) = 0
  rw [congrFun LocalCylinderAlgebra.realizeGlobal_zero sigma]
  norm_num

@[simp] theorem realizeGlobal_one : realizeGlobal 1 = 1 := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal 1 sigma : ℝ) : ℂ) +
    Complex.I * (LocalCylinderAlgebra.realizeGlobal 0 sigma : ℝ) = 1
  rw [congrFun LocalCylinderAlgebra.realizeGlobal_one sigma,
    congrFun LocalCylinderAlgebra.realizeGlobal_zero sigma]
  norm_num

@[simp] theorem realizeGlobal_add (O P : ComplexLocalCylinderAlgebra) :
    realizeGlobal (O + P) = realizeGlobal O + realizeGlobal P := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal (O.re + P.re) sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal (O.im + P.im) sigma : ℝ) =
    (((LocalCylinderAlgebra.realizeGlobal O.re sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal O.im sigma : ℝ)) +
    (((LocalCylinderAlgebra.realizeGlobal P.re sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal P.im sigma : ℝ))
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_add O.re P.re) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_add O.im P.im) sigma]
  simp only [Pi.add_apply]
  push_cast
  ring

@[simp] theorem realizeGlobal_mul (O P : ComplexLocalCylinderAlgebra) :
    realizeGlobal (O * P) = realizeGlobal O * realizeGlobal P := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal
        (O.re * P.re - O.im * P.im) sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal
        (O.re * P.im + O.im * P.re) sigma : ℝ) =
    ((((LocalCylinderAlgebra.realizeGlobal O.re sigma : ℝ) : ℂ) +
        Complex.I * (LocalCylinderAlgebra.realizeGlobal O.im sigma : ℝ)) *
      (((LocalCylinderAlgebra.realizeGlobal P.re sigma : ℝ) : ℂ) +
        Complex.I * (LocalCylinderAlgebra.realizeGlobal P.im sigma : ℝ)))
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_sub
      (O.re * P.re) (O.im * P.im)) sigma]
  simp only [Pi.sub_apply]
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.re P.re) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.im P.im) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_add
      (O.re * P.im) (O.im * P.re)) sigma]
  simp only [Pi.add_apply]
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.re P.im) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.im P.re) sigma]
  simp only [Pi.mul_apply]
  push_cast
  apply Complex.ext <;> simp <;> ring

@[simp] theorem realizeGlobal_neg (O : ComplexLocalCylinderAlgebra) :
    realizeGlobal (-O) = -realizeGlobal O := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal (-O.re) sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal (-O.im) sigma : ℝ) =
    -((((LocalCylinderAlgebra.realizeGlobal O.re sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal O.im sigma : ℝ)))
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_neg O.re) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_neg O.im) sigma]
  simp only [Pi.neg_apply]
  push_cast
  ring

@[simp] theorem realizeGlobal_sub (O P : ComplexLocalCylinderAlgebra) :
    realizeGlobal (O - P) = realizeGlobal O - realizeGlobal P := by
  rw [show O - P = O + -P from rfl, realizeGlobal_add, realizeGlobal_neg]
  rfl

@[simp] theorem realizeGlobal_smul (c : ℂ) (O : ComplexLocalCylinderAlgebra) :
    realizeGlobal (c • O) = c • realizeGlobal O := by
  funext sigma
  change ((LocalCylinderAlgebra.realizeGlobal
        (c.re • O.re - c.im • O.im) sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal
        (c.re • O.im + c.im • O.re) sigma : ℝ) =
    c * ((((LocalCylinderAlgebra.realizeGlobal O.re sigma : ℝ) : ℂ) +
      Complex.I * (LocalCylinderAlgebra.realizeGlobal O.im sigma : ℝ)))
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_sub
      (c.re • O.re) (c.im • O.im)) sigma]
  simp only [Pi.sub_apply]
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_smul c.re O.re) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_smul c.im O.im) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_add
      (c.re • O.im) (c.im • O.re)) sigma]
  simp only [Pi.add_apply]
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_smul c.re O.im) sigma,
    congrFun (LocalCylinderAlgebra.realizeGlobal_smul c.im O.re) sigma]
  simp only [Pi.smul_apply]
  push_cast
  apply Complex.ext <;> simp <;> ring

noncomputable instance : SMul ℕ ComplexLocalCylinderAlgebra :=
  ⟨fun n O => (n : ℂ) • O⟩

noncomputable instance : SMul ℤ ComplexLocalCylinderAlgebra :=
  ⟨fun n O => (n : ℂ) • O⟩

@[simp] theorem realizeGlobal_nsmul (n : ℕ) (O : ComplexLocalCylinderAlgebra) :
    realizeGlobal (n • O) = n • realizeGlobal O := by
  change realizeGlobal ((n : ℂ) • O) = n • realizeGlobal O
  rw [realizeGlobal_smul]
  funext sigma
  simp [nsmul_eq_mul]

@[simp] theorem realizeGlobal_zsmul (n : ℤ) (O : ComplexLocalCylinderAlgebra) :
    realizeGlobal (n • O) = n • realizeGlobal O := by
  change realizeGlobal ((n : ℂ) • O) = n • realizeGlobal O
  rw [realizeGlobal_smul]
  funext sigma
  simp [zsmul_eq_mul]

@[simp] theorem realizeGlobal_pow (O : ComplexLocalCylinderAlgebra) :
    ∀ n : ℕ, realizeGlobal (O ^ n) = realizeGlobal O ^ n
  | 0 => realizeGlobal_one
  | n + 1 => by
      change realizeGlobal ((O ^ n) * O) = realizeGlobal O ^ (n + 1)
      rw [realizeGlobal_mul, realizeGlobal_pow]
      rfl

@[simp] theorem realizeGlobal_natCast (n : ℕ) :
    realizeGlobal (n : ComplexLocalCylinderAlgebra) =
      (n : InfiniteIsingConfig → ℂ) := by
  funext sigma
  change (((n : LocalCylinderAlgebra).realizeGlobal sigma : ℝ) : ℂ) +
    Complex.I * ((0 : LocalCylinderAlgebra).realizeGlobal sigma : ℝ) = n
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_natCast n) sigma,
    congrFun LocalCylinderAlgebra.realizeGlobal_zero sigma]
  norm_num

@[simp] theorem realizeGlobal_intCast (n : ℤ) :
    realizeGlobal (n : ComplexLocalCylinderAlgebra) =
      (n : InfiniteIsingConfig → ℂ) := by
  funext sigma
  change (((n : LocalCylinderAlgebra).realizeGlobal sigma : ℝ) : ℂ) +
    Complex.I * ((0 : LocalCylinderAlgebra).realizeGlobal sigma : ℝ) = n
  rw [congrFun (LocalCylinderAlgebra.realizeGlobal_intCast n) sigma,
    congrFun LocalCylinderAlgebra.realizeGlobal_zero sigma]
  norm_num

noncomputable instance : CommRing ComplexLocalCylinderAlgebra :=
  Function.Injective.commRing realizeGlobal realizeGlobal_injective
    realizeGlobal_zero realizeGlobal_one realizeGlobal_add realizeGlobal_mul
    realizeGlobal_neg realizeGlobal_sub realizeGlobal_nsmul realizeGlobal_zsmul
    realizeGlobal_pow realizeGlobal_natCast realizeGlobal_intCast

noncomputable def realizeGlobalAddHom :
    ComplexLocalCylinderAlgebra →+ (InfiniteIsingConfig → ℂ) where
  toFun := realizeGlobal
  map_zero' := realizeGlobal_zero
  map_add' := realizeGlobal_add

noncomputable instance : Module ℂ ComplexLocalCylinderAlgebra :=
  Function.Injective.module ℂ realizeGlobalAddHom realizeGlobal_injective
    realizeGlobal_smul

/-- Constant complex cylinder. -/
noncomputable def const (c : ℂ) : ComplexLocalCylinderAlgebra :=
  ⟨LocalCylinderAlgebra.const c.re, LocalCylinderAlgebra.const c.im⟩

@[simp] theorem realizeGlobal_const (c : ℂ) :
    realizeGlobal (const c) = fun _ => c := by
  funext sigma
  change (c.re : ℂ) + Complex.I * c.im = c
  rw [mul_comm Complex.I (c.im : ℂ), Complex.re_add_im]

noncomputable def constRingHom : ℂ →+* ComplexLocalCylinderAlgebra where
  toFun := const
  map_zero' := by
    apply realizeGlobal_injective
    rw [realizeGlobal_const, realizeGlobal_zero]
    rfl
  map_one' := by
    apply realizeGlobal_injective
    rw [realizeGlobal_const, realizeGlobal_one]
    rfl
  map_add' c d := by
    apply realizeGlobal_injective
    rw [realizeGlobal_const, realizeGlobal_add,
      realizeGlobal_const, realizeGlobal_const]
    rfl
  map_mul' c d := by
    apply realizeGlobal_injective
    rw [realizeGlobal_const, realizeGlobal_mul,
      realizeGlobal_const, realizeGlobal_const]
    rfl

noncomputable instance : Algebra ℂ ComplexLocalCylinderAlgebra where
  algebraMap := constRingHom
  commutes' := fun _ O => mul_comm _ O
  smul_def' := by
    intro c O
    apply realizeGlobal_injective
    rw [realizeGlobal_smul, realizeGlobal_mul]
    funext sigma
    change c * realizeGlobal O sigma =
      realizeGlobal (constRingHom c) sigma * realizeGlobal O sigma
    have hc : realizeGlobal (constRingHom c) sigma = c := by
      exact congrFun (realizeGlobal_const c) sigma
    rw [hc]

noncomputable instance : Star ComplexLocalCylinderAlgebra :=
  ⟨fun O => ⟨O.re, -O.im⟩⟩

@[simp] theorem star_re (O : ComplexLocalCylinderAlgebra) : (star O).re = O.re := rfl
@[simp] theorem star_im (O : ComplexLocalCylinderAlgebra) : (star O).im = -O.im := rfl

noncomputable instance : InvolutiveStar ComplexLocalCylinderAlgebra where
  star_involutive O := by
    cases O with
    | mk Ore Oim =>
        change ComplexLocalCylinderAlgebra.mk Ore (- -Oim) =
          ComplexLocalCylinderAlgebra.mk Ore Oim
        rw [neg_neg]

@[simp] theorem realizeGlobal_star (O : ComplexLocalCylinderAlgebra) :
    realizeGlobal (star O) = star (realizeGlobal O) := by
  funext sigma
  simp only [realizeGlobal, star_re, star_im,
    LocalCylinderAlgebra.realizeGlobal_neg, Pi.neg_apply, Pi.star_apply]
  push_cast
  apply Complex.ext <;> simp

noncomputable instance : StarRing ComplexLocalCylinderAlgebra where
  star_mul O P := by
    apply realizeGlobal_injective
    rw [realizeGlobal_star, realizeGlobal_mul, realizeGlobal_mul,
      realizeGlobal_star, realizeGlobal_star]
    exact star_mul _ _
  star_add O P := by
    apply realizeGlobal_injective
    rw [realizeGlobal_star, realizeGlobal_add, realizeGlobal_add,
      realizeGlobal_star, realizeGlobal_star]
    exact star_add _ _

noncomputable instance : StarModule ℂ ComplexLocalCylinderAlgebra where
  star_smul c O := by
    apply realizeGlobal_injective
    rw [realizeGlobal_star, realizeGlobal_smul, realizeGlobal_smul,
      realizeGlobal_star]
    exact star_smul _ _

noncomputable def realizeGlobalStarAlgHom :
    ComplexLocalCylinderAlgebra →⋆ₐ[ℂ] (InfiniteIsingConfig → ℂ) where
  toFun := realizeGlobal
  map_one' := realizeGlobal_one
  map_mul' := realizeGlobal_mul
  map_zero' := realizeGlobal_zero
  map_add' := realizeGlobal_add
  commutes' c := by
    funext sigma
    exact congrFun (realizeGlobal_const c) sigma
  map_star' := realizeGlobal_star

theorem realizeGlobalStarAlgHom_injective :
    Function.Injective realizeGlobalStarAlgHom := realizeGlobal_injective

/-! ## Bounded continuous realization and the concrete C-star closure -/

theorem continuous_realizeGlobal (O : ComplexLocalCylinderAlgebra) :
    Continuous O.realizeGlobal := by
  unfold realizeGlobal
  exact (Complex.continuous_ofReal.comp O.re.continuous_realizeGlobal).add
    (continuous_const.mul
      (Complex.continuous_ofReal.comp O.im.continuous_realizeGlobal))

noncomputable def toBoundedContinuousFunction (O : ComplexLocalCylinderAlgebra) :
    InfiniteIsingConfig →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact ⟨O.realizeGlobal, O.continuous_realizeGlobal⟩

@[simp] theorem toBoundedContinuousFunction_apply
    (O : ComplexLocalCylinderAlgebra) (sigma : InfiniteIsingConfig) :
    O.toBoundedContinuousFunction sigma = O.realizeGlobal sigma := rfl

noncomputable def realizeGlobalBCFStarAlgHom :
    ComplexLocalCylinderAlgebra →⋆ₐ[ℂ] (InfiniteIsingConfig →ᵇ ℂ) where
  toFun := toBoundedContinuousFunction
  map_one' := by ext sigma; exact congrFun realizeGlobal_one sigma
  map_mul' O P := by ext sigma; exact congrFun (realizeGlobal_mul O P) sigma
  map_zero' := by ext sigma; exact congrFun realizeGlobal_zero sigma
  map_add' O P := by ext sigma; exact congrFun (realizeGlobal_add O P) sigma
  commutes' c := by
    ext sigma
    change realizeGlobal (constRingHom c) sigma = c
    exact congrFun (realizeGlobal_const c) sigma
  map_star' O := by ext sigma; exact congrFun (realizeGlobal_star O) sigma

theorem realizeGlobalBCFStarAlgHom_injective :
    Function.Injective realizeGlobalBCFStarAlgHom := by
  intro O P h
  apply realizeGlobal_injective
  funext sigma
  exact DFunLike.congr_fun h sigma

noncomputable instance : NormedCommRing ComplexLocalCylinderAlgebra :=
  NormedCommRing.induced ComplexLocalCylinderAlgebra
    (InfiniteIsingConfig →ᵇ ℂ) realizeGlobalBCFStarAlgHom
    realizeGlobalBCFStarAlgHom_injective

noncomputable instance : NormedSpace ℂ ComplexLocalCylinderAlgebra :=
  NormedSpace.induced ℂ ComplexLocalCylinderAlgebra
    (InfiniteIsingConfig →ᵇ ℂ) realizeGlobalBCFStarAlgHom

noncomputable instance : NormedAlgebra ℂ ComplexLocalCylinderAlgebra :=
  NormedAlgebra.induced ℂ ComplexLocalCylinderAlgebra
    (InfiniteIsingConfig →ᵇ ℂ) realizeGlobalBCFStarAlgHom

/-- The represented finite-support complex star algebra. -/
noncomputable abbrev LocalComplexStarAlgebra :
    StarSubalgebra ℂ (InfiniteIsingConfig →ᵇ ℂ) :=
  realizeGlobalBCFStarAlgHom.range

/-- The quasilocal commutative C-star algebra: uniform closure of complex
finite-support cylinders. -/
noncomputable abbrev QuasilocalCStarAlgebra :
    StarSubalgebra ℂ (InfiniteIsingConfig →ᵇ ℂ) :=
  LocalComplexStarAlgebra.topologicalClosure

noncomputable instance : Nontrivial QuasilocalCStarAlgebra := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have heval : (0 : ℂ) = 1 := by
    simpa using congrArg
      (fun F : QuasilocalCStarAlgebra ↦
        ((F : InfiniteIsingConfig →ᵇ ℂ) (fun _ ↦ 0))) h
  exact zero_ne_one heval

noncomputable instance : CommCStarAlgebra QuasilocalCStarAlgebra :=
  StarSubalgebra.commCStarAlgebra _
    (h_closed := StarSubalgebra.isClosed_topologicalClosure _)

noncomputable instance : NormedStarGroup QuasilocalCStarAlgebra where
  norm_star_le x := by
    change ‖star (x : InfiniteIsingConfig →ᵇ ℂ)‖ ≤
      ‖(x : InfiniteIsingConfig →ᵇ ℂ)‖
    rw [norm_star]

noncomputable instance : ContinuousStar QuasilocalCStarAlgebra :=
  NormedStarGroup.to_continuousStar

noncomputable instance : IsTopologicalRing QuasilocalCStarAlgebra :=
  NonUnitalSeminormedRing.toIsTopologicalRing

noncomputable instance : T0Space QuasilocalCStarAlgebra :=
  MetricSpace.instT0Space

noncomputable instance : T3Space QuasilocalCStarAlgebra := ⟨⟩

noncomputable instance : T25Space QuasilocalCStarAlgebra :=
  T3Space.t25Space

noncomputable instance : T2Space QuasilocalCStarAlgebra :=
  T25Space.t2Space

noncomputable instance :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      QuasilocalCStarAlgebra IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus

noncomputable instance : PartialOrder QuasilocalCStarAlgebra :=
  CStarAlgebra.spectralOrder _

noncomputable instance : StarOrderedRing QuasilocalCStarAlgebra :=
  CStarAlgebra.spectralOrderedRing _

noncomputable instance : Norm (QuasilocalCStarAlgebra →L[ℂ] ℂ) :=
  ContinuousLinearMap.hasOpNorm

/-! ## The local complex functional and its norm bound -/

section State

variable (beta gamma alpha : ℝ)
variable (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
variable (hwin : 2 * Real.tanh |beta| + 2 * Real.tanh |gamma| ≤ alpha)

/-- Complexification of the Dobrushin state on local cylinders. -/
noncomputable def complexStateValue (O : ComplexLocalCylinderAlgebra) : ℂ :=
  (LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin O.re : ℂ) +
    Complex.I *
      (LocalCylinderAlgebra.infiniteStateValue
        beta gamma alpha halpha0 halpha1 hwin O.im : ℂ)

theorem complexStateValue_add (O P : ComplexLocalCylinderAlgebra) :
    complexStateValue beta gamma alpha halpha0 halpha1 hwin (O + P) =
      complexStateValue beta gamma alpha halpha0 halpha1 hwin O +
        complexStateValue beta gamma alpha halpha0 halpha1 hwin P := by
  change ((LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin (O.re + P.re) : ℝ) : ℂ) +
      Complex.I * ((LocalCylinderAlgebra.infiniteStateValue
        beta gamma alpha halpha0 halpha1 hwin (O.im + P.im) : ℝ) : ℂ) =
      (((LocalCylinderAlgebra.infiniteStateValue
          beta gamma alpha halpha0 halpha1 hwin O.re : ℝ) : ℂ) +
        Complex.I * ((LocalCylinderAlgebra.infiniteStateValue
          beta gamma alpha halpha0 halpha1 hwin O.im : ℝ) : ℂ)) +
      (((LocalCylinderAlgebra.infiniteStateValue
          beta gamma alpha halpha0 halpha1 hwin P.re : ℝ) : ℂ) +
        Complex.I * ((LocalCylinderAlgebra.infiniteStateValue
          beta gamma alpha halpha0 halpha1 hwin P.im : ℝ) : ℂ))
  simp only [
    LocalCylinderAlgebra.infiniteStateValue_add]
  push_cast
  ring

theorem complexStateValue_smul (c : ℂ) (O : ComplexLocalCylinderAlgebra) :
    complexStateValue beta gamma alpha halpha0 halpha1 hwin (c • O) =
      c * complexStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  change ((LocalCylinderAlgebra.infiniteStateValue beta gamma alpha
      halpha0 halpha1 hwin (c.re • O.re - c.im • O.im) : ℝ) : ℂ) +
      Complex.I * ((LocalCylinderAlgebra.infiniteStateValue beta gamma alpha
        halpha0 halpha1 hwin (c.re • O.im + c.im • O.re) : ℝ) : ℂ) =
      c * (((LocalCylinderAlgebra.infiniteStateValue beta gamma alpha
          halpha0 halpha1 hwin O.re : ℝ) : ℂ) +
        Complex.I * ((LocalCylinderAlgebra.infiniteStateValue beta gamma alpha
          halpha0 halpha1 hwin O.im : ℝ) : ℂ))
  simp only [
    sub_eq_add_neg,
    LocalCylinderAlgebra.infiniteStateValue_add,
    LocalCylinderAlgebra.infiniteStateValue_neg,
    LocalCylinderAlgebra.infiniteStateValue_smul]
  push_cast
  apply Complex.ext <;> simp <;> ring

noncomputable def complexStateLinearMap : ComplexLocalCylinderAlgebra →ₗ[ℂ] ℂ where
  toFun := complexStateValue beta gamma alpha halpha0 halpha1 hwin
  map_add' := complexStateValue_add beta gamma alpha halpha0 halpha1 hwin
  map_smul' := complexStateValue_smul beta gamma alpha halpha0 halpha1 hwin

theorem uniformNorm_re_le_norm (O : ComplexLocalCylinderAlgebra) :
    LocalCylinderAlgebra.uniformNorm O.re ≤ ‖O‖ := by
  apply csSup_le
  · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
  · rintro y ⟨sigma, rfl⟩
    calc
      |O.re.realizeGlobal sigma| = |(O.realizeGlobal sigma).re| := by
        simp [realizeGlobal]
      _ ≤ ‖O.realizeGlobal sigma‖ := Complex.abs_re_le_norm _
      _ = ‖O.toBoundedContinuousFunction sigma‖ := rfl
      _ ≤ ‖O.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ _
      _ = ‖O‖ := rfl

theorem uniformNorm_im_le_norm (O : ComplexLocalCylinderAlgebra) :
    LocalCylinderAlgebra.uniformNorm O.im ≤ ‖O‖ := by
  apply csSup_le
  · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
  · rintro y ⟨sigma, rfl⟩
    calc
      |O.im.realizeGlobal sigma| = |(O.realizeGlobal sigma).im| := by
        simp [realizeGlobal]
      _ ≤ ‖O.realizeGlobal sigma‖ := Complex.abs_im_le_norm _
      _ = ‖O.toBoundedContinuousFunction sigma‖ := rfl
      _ ≤ ‖O.toBoundedContinuousFunction‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ _
      _ = ‖O‖ := rfl

theorem norm_complexStateValue_le (O : ComplexLocalCylinderAlgebra) :
    ‖complexStateValue beta gamma alpha halpha0 halpha1 hwin O‖ ≤ 2 * ‖O‖ := by
  let wr := LocalCylinderAlgebra.infiniteStateValue
    beta gamma alpha halpha0 halpha1 hwin O.re
  let wi := LocalCylinderAlgebra.infiniteStateValue
    beta gamma alpha halpha0 halpha1 hwin O.im
  calc
    ‖complexStateValue beta gamma alpha halpha0 halpha1 hwin O‖ =
        ‖(wr : ℂ) + Complex.I * (wi : ℂ)‖ := rfl
    _ ≤ ‖(wr : ℂ)‖ + ‖Complex.I * (wi : ℂ)‖ := norm_add_le _ _
    _ = |wr| + |wi| := by simp [Complex.norm_real]
    _ ≤ LocalCylinderAlgebra.uniformNorm O.re +
        LocalCylinderAlgebra.uniformNorm O.im :=
      add_le_add
        (LocalCylinderAlgebra.abs_infiniteStateValue_le_uniformNorm
          beta gamma alpha halpha0 halpha1 hwin O.re)
        (LocalCylinderAlgebra.abs_infiniteStateValue_le_uniformNorm
          beta gamma alpha halpha0 halpha1 hwin O.im)
    _ ≤ ‖O‖ + ‖O‖ := add_le_add (uniformNorm_re_le_norm O) (uniformNorm_im_le_norm O)
    _ = 2 * ‖O‖ := by ring

/-- Continuous local complex state.  The explicit constant `2` suffices for
extension; positivity will later recover norm one on the completed algebra. -/
noncomputable def complexStateCLM : ComplexLocalCylinderAlgebra →L[ℂ] ℂ :=
  (complexStateLinearMap beta gamma alpha halpha0 halpha1 hwin).mkContinuous 2
    (norm_complexStateValue_le beta gamma alpha halpha0 halpha1 hwin)

theorem infiniteStateValue_zero :
    LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin 0 = 0 := by
  rw [← zero_smul ℝ (1 : LocalCylinderAlgebra),
    LocalCylinderAlgebra.infiniteStateValue_smul, zero_mul]

theorem complexStateValue_one :
    complexStateValue beta gamma alpha halpha0 halpha1 hwin 1 = 1 := by
  change ((LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin 1 : ℝ) : ℂ) +
    Complex.I * ((LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin 0 : ℝ) : ℂ) = 1
  rw [LocalCylinderAlgebra.infiniteStateValue_one,
    infiniteStateValue_zero beta gamma alpha halpha0 halpha1 hwin]
  norm_num

theorem complexStateValue_star_mul_self_nonneg
    (O : ComplexLocalCylinderAlgebra) :
    0 ≤ complexStateValue beta gamma alpha halpha0 halpha1 hwin (star O * O) := by
  rw [Complex.nonneg_iff]
  simp only [complexStateValue, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul,
    Complex.ofReal_im, mul_zero, sub_zero, zero_add, add_zero, mul_re, mul_im,
    star_re, star_im]
  constructor
  · change 0 ≤ LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin
        (O.re * O.re - (-O.im) * O.im)
    have hre : O.re * O.re - (-O.im) * O.im =
        O.re * O.re + O.im * O.im := by ring
    rw [hre]
    apply LocalCylinderAlgebra.infiniteStateValue_nonneg
    intro sigma
    rw [congrFun (LocalCylinderAlgebra.realizeGlobal_add
      (O.re * O.re) (O.im * O.im)) sigma]
    simp only [Pi.add_apply]
    rw [congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.re O.re) sigma,
      congrFun (LocalCylinderAlgebra.realizeGlobal_mul O.im O.im) sigma]
    simp only [Pi.mul_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  · change 0 = LocalCylinderAlgebra.infiniteStateValue
      beta gamma alpha halpha0 halpha1 hwin
        (O.re * O.im + (-O.im) * O.re)
    have him : O.re * O.im + (-O.im) * O.re = 0 := by ring
    rw [him, infiniteStateValue_zero beta gamma alpha halpha0 halpha1 hwin]

theorem norm_complexStateValue_le_uniform
    (O : ComplexLocalCylinderAlgebra) :
    ‖complexStateValue beta gamma alpha halpha0 halpha1 hwin O‖ ≤ ‖O‖ := by
  let z := complexStateValue beta gamma alpha halpha0 halpha1 hwin O
  by_cases hz : z = 0
  · simp [z, hz]
  let c : ℂ := star z / (‖z‖ : ℂ)
  have hnormz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hcnorm : ‖c‖ = 1 := by
    simp [c, norm_div, hnormz]
  have hcz : c * z = (‖z‖ : ℂ) := by
    calc
      c * z = (star z * z) / (‖z‖ : ℂ) := by
        simp only [c, div_mul_eq_mul_div]
      _ = (Complex.normSq z : ℂ) / (‖z‖ : ℂ) := by
        change ((starRingEnd ℂ) z * z) / (‖z‖ : ℂ) = _
        rw [← Complex.normSq_eq_conj_mul_self]
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = (‖z‖ : ℂ) := by
        push_cast
        field_simp [hnormz]
  have hrestate :
      LocalCylinderAlgebra.infiniteStateValue
          beta gamma alpha halpha0 halpha1 hwin (c • O).re = ‖z‖ := by
    have hmap := complexStateValue_smul
      beta gamma alpha halpha0 halpha1 hwin c O
    rw [show complexStateValue beta gamma alpha halpha0 halpha1 hwin O = z from rfl,
      hcz] at hmap
    have hre := congrArg Complex.re hmap
    simpa only [complexStateValue, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero] using hre
  calc
    ‖complexStateValue beta gamma alpha halpha0 halpha1 hwin O‖ = ‖z‖ := rfl
    _ = |LocalCylinderAlgebra.infiniteStateValue
        beta gamma alpha halpha0 halpha1 hwin (c • O).re| := by
      rw [hrestate, abs_of_nonneg (norm_nonneg z)]
    _ ≤ LocalCylinderAlgebra.uniformNorm (c • O).re :=
      LocalCylinderAlgebra.abs_infiniteStateValue_le_uniformNorm
        beta gamma alpha halpha0 halpha1 hwin (c • O).re
    _ ≤ ‖c • O‖ := uniformNorm_re_le_norm (c • O)
    _ = ‖c‖ * ‖O‖ := norm_smul c O
    _ = ‖O‖ := by rw [hcnorm, one_mul]

/-! ## Dense embedding and extension to the C-star closure -/

noncomputable def localToQuasilocalStarAlgHom :
    ComplexLocalCylinderAlgebra →⋆ₐ[ℂ] QuasilocalCStarAlgebra where
  toFun O := ⟨realizeGlobalBCFStarAlgHom O,
    StarSubalgebra.le_topologicalClosure _ ⟨O, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one realizeGlobalBCFStarAlgHom
  map_mul' O P := by apply Subtype.ext; exact map_mul realizeGlobalBCFStarAlgHom O P
  map_zero' := by apply Subtype.ext; exact map_zero realizeGlobalBCFStarAlgHom
  map_add' O P := by apply Subtype.ext; exact map_add realizeGlobalBCFStarAlgHom O P
  commutes' c := by apply Subtype.ext; exact realizeGlobalBCFStarAlgHom.commutes c
  map_star' O := by apply Subtype.ext; exact map_star realizeGlobalBCFStarAlgHom O

noncomputable def localToQuasilocalLinearIsometry :
    ComplexLocalCylinderAlgebra →ₗᵢ[ℂ] QuasilocalCStarAlgebra where
  toLinearMap :=
    localToQuasilocalStarAlgHom.toAlgHom.toLinearMap
  norm_map' _ := rfl

/-- The dense local inclusion, named at its continuous-linear-map type so that
extension lemmas do not have to unfold the isometry coercion. -/
noncomputable def localToQuasilocalCLM :
    ComplexLocalCylinderAlgebra →L[ℂ] QuasilocalCStarAlgebra :=
  localToQuasilocalLinearIsometry.toContinuousLinearMap

theorem denseRange_localToQuasilocal :
    DenseRange localToQuasilocalLinearIsometry := by
  change DenseRange
    (localToQuasilocalStarAlgHom :
      ComplexLocalCylinderAlgebra → QuasilocalCStarAlgebra)
  let rangeLift : ComplexLocalCylinderAlgebra → LocalComplexStarAlgebra :=
    fun O => ⟨realizeGlobalBCFStarAlgHom O, ⟨O, rfl⟩⟩
  have hrange : Function.Surjective rangeLift := by
    rintro ⟨F, ⟨O, rfl⟩⟩
    exact ⟨O, rfl⟩
  have hinclusion : DenseRange
      (Set.inclusion
        (StarSubalgebra.le_topologicalClosure LocalComplexStarAlgebra)) := by
    exact (denseRange_inclusion_iff
      (StarSubalgebra.le_topologicalClosure LocalComplexStarAlgebra)).2 subset_rfl
  simpa [localToQuasilocalLinearIsometry, localToQuasilocalStarAlgHom,
    rangeLift] using hinclusion.comp hrange.denseRange
      (continuous_inclusion
        (StarSubalgebra.le_topologicalClosure LocalComplexStarAlgebra))

theorem denseRange_localToQuasilocalCLM :
    DenseRange localToQuasilocalCLM := by
  exact denseRange_localToQuasilocal

theorem isUniformInducing_localToQuasilocalCLM :
    IsUniformInducing localToQuasilocalCLM := by
  exact localToQuasilocalLinearIsometry.isometry.isUniformInducing

/-- Continuous extension from the represented local algebra to its uniform
C-star closure. -/
noncomputable def quasilocalStateCLM : QuasilocalCStarAlgebra →L[ℂ] ℂ :=
  (complexStateCLM beta gamma alpha halpha0 halpha1 hwin).extend
    localToQuasilocalCLM

theorem quasilocalStateCLM_inclusion (O : ComplexLocalCylinderAlgebra) :
    quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
        (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)
        (localToQuasilocalLinearIsometry O) =
      complexStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  change (complexStateCLM beta gamma alpha halpha0 halpha1 hwin).extend
      localToQuasilocalCLM (localToQuasilocalCLM O) =
    complexStateCLM beta gamma alpha halpha0 halpha1 hwin O
  exact ContinuousLinearMap.extend_eq
    (complexStateCLM beta gamma alpha halpha0 halpha1 hwin)
    denseRange_localToQuasilocalCLM
    isUniformInducing_localToQuasilocalCLM O

theorem quasilocalStateCLM_local (O : ComplexLocalCylinderAlgebra) :
    quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
        (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)
        (localToQuasilocalStarAlgHom O) =
      complexStateValue beta gamma alpha halpha0 halpha1 hwin O := by
  change quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)
      (localToQuasilocalLinearIsometry O) = _
  exact quasilocalStateCLM_inclusion beta gamma alpha halpha0 halpha1 hwin O

theorem quasilocalStateCLM_star_mul_self_nonneg
    (x : QuasilocalCStarAlgebra) :
    0 ≤ quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin) (star x * x) := by
  refine denseRange_localToQuasilocal.induction_on x ?_ ?_
  · exact isClosed_le continuous_const
      ((quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
        (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)).continuous.comp
          (continuous_id.star.mul continuous_id))
  · intro F
    change 0 ≤ quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)
        (star (localToQuasilocalStarAlgHom F) * localToQuasilocalStarAlgHom F)
    rw [← map_star, ← map_mul]
    rw [quasilocalStateCLM_local]
    exact complexStateValue_star_mul_self_nonneg
      beta gamma alpha halpha0 halpha1 hwin F

theorem quasilocalStateCLM_nonneg {x : QuasilocalCStarAlgebra} (hx : 0 ≤ x) :
    0 ≤ quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin) x := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact quasilocalStateCLM_star_mul_self_nonneg
    beta gamma alpha halpha0 halpha1 hwin a

theorem quasilocalStateCLM_one :
    quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin) 1 = 1 := by
  rw [← map_one localToQuasilocalStarAlgHom]
  change quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)
        (localToQuasilocalLinearIsometry 1) = 1
  rw [quasilocalStateCLM_inclusion]
  exact complexStateValue_one beta gamma alpha halpha0 halpha1 hwin

theorem norm_quasilocalStateCLM_apply_le (x : QuasilocalCStarAlgebra) :
    ‖quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin) x‖ ≤ ‖x‖ := by
  refine denseRange_localToQuasilocal.induction_on x ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp
        (quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
          (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)).continuous)
      continuous_norm
  · intro F
    rw [quasilocalStateCLM_inclusion]
    simpa using norm_complexStateValue_le_uniform
      beta gamma alpha halpha0 halpha1 hwin F

theorem norm_quasilocalStateCLM :
    ‖quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using norm_quasilocalStateCLM_apply_le
      beta gamma alpha halpha0 halpha1 hwin x
  · calc
      1 = ‖(quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
          (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin))
          (1 : QuasilocalCStarAlgebra)‖ := by
            rw [quasilocalStateCLM_one, norm_one]
      _ ≤ ‖quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
          (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)‖ *
            ‖(1 : QuasilocalCStarAlgebra)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
          (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)‖ := by
        rw [norm_one, mul_one]

/-- The positive normalized functional on the quasilocal commutative C-star
algebra. -/
noncomputable def quasilocalCStarState : QuasilocalCStarAlgebra →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    (quasilocalStateCLM (beta := beta) (gamma := gamma) (alpha := alpha)
      (halpha0 := halpha0) (halpha1 := halpha1) (hwin := hwin)).toLinearMap
    fun _ hx => quasilocalStateCLM_nonneg
      beta gamma alpha halpha0 halpha1 hwin hx

theorem quasilocalCStarState_map_one :
    quasilocalCStarState beta gamma alpha halpha0 halpha1 hwin 1 = 1 :=
  quasilocalStateCLM_one beta gamma alpha halpha0 halpha1 hwin

end State

end ComplexLocalCylinderAlgebra
end Dobrushin
end YangMills.OS
