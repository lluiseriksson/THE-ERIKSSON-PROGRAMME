/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernelReindex
import YangMills.RG.BalabanCMP99PhysicalFibreComplexification

/-!
# Canonical complexification of finite counting-Hilbert operators

PRE-VALIDATION: source present; `.olean` not yet materialized; result not yet
verified by the compiler.

A real operator on a finite `PiLp` field has a canonical complex-linear
extension: apply it independently to the real and imaginary parts and
recombine.  This file constructs that extension internally and proves that it
preserves identities and composition.  Those two laws are the load-bearing
ones for transporting a real inverse certificate to the literal complex
precision; no complex operator family or inverse equality is accepted as
input.
-/

namespace YangMills.RG

open YangMills

noncomputable section

universe u v

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

/-- Coordinatewise real part of a finite complex Euclidean field. -/
def finitePiLpComplexRealPart
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    FinitePiLpField ι (EuclideanSpace ℝ κ) :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => (z i a).re

/-- Coordinatewise imaginary part of a finite complex Euclidean field. -/
def finitePiLpComplexImagPart
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    FinitePiLpField ι (EuclideanSpace ℝ κ) :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => (z i a).im

/-- Coordinatewise inclusion of a finite real Euclidean field into its
complexification. -/
def finitePiLpComplexOfReal
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    FinitePiLpField ι (EuclideanSpace ℂ κ) :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => (x i a : ℂ)

omit [Fintype ι] [Fintype κ] in
@[simp] theorem finitePiLpComplexRealPart_apply
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) (i : ι) (a : κ) :
    finitePiLpComplexRealPart z i a = (z i a).re := rfl

omit [Fintype ι] [Fintype κ] in
@[simp] theorem finitePiLpComplexImagPart_apply
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) (i : ι) (a : κ) :
    finitePiLpComplexImagPart z i a = (z i a).im := rfl

omit [Fintype ι] [Fintype κ] in
@[simp] theorem finitePiLpComplexOfReal_apply
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) (i : ι) (a : κ) :
    finitePiLpComplexOfReal x i a = (x i a : ℂ) := rfl

theorem finitePiLpComplexRealPart_add
    (z w : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexRealPart (z + w) =
      finitePiLpComplexRealPart z + finitePiLpComplexRealPart w := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

theorem finitePiLpComplexImagPart_add
    (z w : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexImagPart (z + w) =
      finitePiLpComplexImagPart z + finitePiLpComplexImagPart w := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

theorem finitePiLpComplexRealPart_smul
    (c : ℂ) (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexRealPart (c • z) =
      c.re • finitePiLpComplexRealPart z -
        c.im • finitePiLpComplexImagPart z := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp [Complex.mul_re]

theorem finitePiLpComplexImagPart_smul
    (c : ℂ) (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexImagPart (c • z) =
      c.im • finitePiLpComplexRealPart z +
        c.re • finitePiLpComplexImagPart z := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp [Complex.mul_im]
  ring

/-- Every finite complex field is its real part plus `i` times its imaginary
part, with both parts embedded through the canonical real inclusion. -/
theorem finitePiLpComplexOfReal_real_add_I_smul_imag
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexOfReal (finitePiLpComplexRealPart z) +
        Complex.I • finitePiLpComplexOfReal (finitePiLpComplexImagPart z) = z := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  apply Complex.ext <;> simp

omit [Fintype ι] [Fintype κ] in
@[simp] theorem finitePiLpComplexRealPart_ofReal
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpComplexRealPart (finitePiLpComplexOfReal x) = x := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

omit [Fintype ι] [Fintype κ] in
@[simp] theorem finitePiLpComplexImagPart_ofReal
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpComplexImagPart (finitePiLpComplexOfReal x) = 0 := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

/-- Canonical complex-linear extension of a real operator on a finite
counting-Hilbert field. -/
noncomputable def finitePiLpCanonicalComplexificationLM
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →ₗ[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    FinitePiLpField ι (EuclideanSpace ℂ κ) →ₗ[ℂ]
      FinitePiLpField ι (EuclideanSpace ℂ κ) where
  toFun z :=
    finitePiLpComplexOfReal (T (finitePiLpComplexRealPart z)) +
      Complex.I • finitePiLpComplexOfReal (T (finitePiLpComplexImagPart z))
  map_add' z w := by
    rw [finitePiLpComplexRealPart_add, finitePiLpComplexImagPart_add,
      map_add, map_add]
    apply PiLp.ext
    intro i
    apply PiLp.ext
    intro a
    simp
    ring
  map_smul' c z := by
    rw [finitePiLpComplexRealPart_smul, finitePiLpComplexImagPart_smul,
      map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
    apply PiLp.ext
    intro i
    apply PiLp.ext
    intro a
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Continuous packaging of the canonical complexification.  Continuity is
automatic because both counting-Hilbert spaces are finite-dimensional. -/
noncomputable def finitePiLpCanonicalComplexificationCLM
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    FinitePiLpField ι (EuclideanSpace ℂ κ) →L[ℂ]
      FinitePiLpField ι (EuclideanSpace ℂ κ) :=
  LinearMap.toContinuousLinearMap
    (finitePiLpCanonicalComplexificationLM T.toLinearMap)

@[simp] theorem finitePiLpCanonicalComplexificationCLM_apply
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpCanonicalComplexificationCLM T z =
      finitePiLpComplexOfReal (T (finitePiLpComplexRealPart z)) +
        Complex.I • finitePiLpComplexOfReal
          (T (finitePiLpComplexImagPart z)) := rfl

@[simp] theorem finitePiLpComplexRealPart_complexification
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexRealPart (finitePiLpCanonicalComplexificationCLM T z) =
      T (finitePiLpComplexRealPart z) := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

@[simp] theorem finitePiLpComplexImagPart_complexification
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (z : FinitePiLpField ι (EuclideanSpace ℂ κ)) :
    finitePiLpComplexImagPart (finitePiLpCanonicalComplexificationCLM T z) =
      T (finitePiLpComplexImagPart z) := by
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro a
  simp

@[simp] theorem finitePiLpCanonicalComplexificationCLM_ofReal
    (T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ))
    (x : FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpCanonicalComplexificationCLM T (finitePiLpComplexOfReal x) =
      finitePiLpComplexOfReal (T x) := by
  simp [finitePiLpCanonicalComplexificationCLM_apply]

/-- Canonical complexification preserves composition exactly. -/
theorem finitePiLpCanonicalComplexificationCLM_comp
    (S T : FinitePiLpField ι (EuclideanSpace ℝ κ) →L[ℝ]
      FinitePiLpField ι (EuclideanSpace ℝ κ)) :
    finitePiLpCanonicalComplexificationCLM (S.comp T) =
      (finitePiLpCanonicalComplexificationCLM S).comp
      (finitePiLpCanonicalComplexificationCLM T) := by
  apply ContinuousLinearMap.ext
  intro z
  change
    finitePiLpComplexOfReal
          ((S.comp T) (finitePiLpComplexRealPart z)) +
        Complex.I • finitePiLpComplexOfReal
          ((S.comp T) (finitePiLpComplexImagPart z)) =
      finitePiLpCanonicalComplexificationCLM S
        (finitePiLpCanonicalComplexificationCLM T z)
  rw [ContinuousLinearMap.comp_apply,
    finitePiLpCanonicalComplexificationCLM_apply,
    finitePiLpComplexRealPart_complexification,
    finitePiLpComplexImagPart_complexification]

/-- Canonical complexification sends the real identity to the complex
identity. -/
theorem finitePiLpCanonicalComplexificationCLM_id :
    finitePiLpCanonicalComplexificationCLM
        (ContinuousLinearMap.id ℝ
          (FinitePiLpField ι (EuclideanSpace ℝ κ))) =
      ContinuousLinearMap.id ℂ
        (FinitePiLpField ι (EuclideanSpace ℂ κ)) := by
  apply ContinuousLinearMap.ext
  intro z
  exact finitePiLpComplexOfReal_real_add_I_smul_imag z

end

end YangMills.RG
