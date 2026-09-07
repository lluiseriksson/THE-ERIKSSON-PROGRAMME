/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98PhysicalNonlinearBlock
import Mathlib.LinearAlgebra.Projection

/-!
# A continuous linear retraction onto the physical `su(N)` coordinates

To compare the derivative of the ambient CMP98 logarithm with the derivative
of its physical `SUNLieCoord` lift, we need continuous linear maps in both
directions.  The inclusion is immediate.  For the reverse map we choose an
algebraic complement of the real subspace `su(N)` inside the finite
matrix space and project along that complement.

The choice of complement is irrelevant on physical matrices: the projection
is proved to be the identity on `su(N)`.  Thus this construction is not a
projection used to redefine a physical field.  It is a calculus device whose
only source-facing endpoint is the exact retraction law.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- A chosen real-linear complement of `su(N)` in the ambient complex
matrix space. -/
noncomputable def cmp98SuMatrixComplement (Nc : ℕ) :
    Submodule ℝ (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  Classical.choose (suMatrixSubmodule Nc).exists_isCompl

/-- The chosen complement really is complementary to `su(N)`. -/
theorem cmp98SuMatrixComplement_isCompl (Nc : ℕ) :
    IsCompl (suMatrixSubmodule Nc) (cmp98SuMatrixComplement Nc) :=
  Classical.choose_spec (suMatrixSubmodule Nc).exists_isCompl

/-- Algebraic projection from the ambient matrix space to the physical Lie
subspace. -/
noncomputable def cmp98AmbientToSuLieLinearMap (Nc : ℕ) :
    Matrix (Fin Nc) (Fin Nc) ℂ →ₗ[ℝ] SuLie Nc :=
  (suMatrixSubmodule Nc).linearProjOfIsCompl
    (cmp98SuMatrixComplement Nc)
    (cmp98SuMatrixComplement_isCompl Nc)

/-- The algebraic projection fixes every physical Lie matrix exactly. -/
@[simp] theorem cmp98AmbientToSuLieLinearMap_apply_mem
    (X : SuLie Nc) :
    cmp98AmbientToSuLieLinearMap Nc X.toMatrix = X := by
  exact Submodule.linearProjOfIsCompl_apply_left
    (cmp98SuMatrixComplement_isCompl Nc) X

/-- Projection followed by the canonical Euclidean coordinates. -/
noncomputable def cmp98AmbientToLieCoordLinearMap (Nc : ℕ) [NeZero Nc] :
    Matrix (Fin Nc) (Fin Nc) ℂ →ₗ[ℝ] SUNLieCoord Nc :=
  (suLieCoordIso Nc).toLinearEquiv.toLinearMap.comp
    (cmp98AmbientToSuLieLinearMap Nc)

/-- Finite dimensionality makes the preceding source map continuous for the
ambient operator norm. -/
noncomputable def cmp98AmbientToLieCoordCLM (Nc : ℕ) [NeZero Nc] :
    Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] SUNLieCoord Nc := by
  let L := cmp98AmbientToLieCoordLinearMap Nc
  have hL : Continuous
      (L : Matrix (Fin Nc) (Fin Nc) ℂ → SUNLieCoord Nc) :=
    @LinearMap.continuous_of_finiteDimensional
      ℝ inferInstance
      (Matrix (Fin Nc) (Fin Nc) ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (SUNLieCoord Nc)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (Module.Finite.matrix) L
  exact ⟨L, hL⟩

/-- Decoding canonical coordinates back to their underlying matrix. -/
noncomputable def cmp98LieCoordToAmbientLinearMap (Nc : ℕ) [NeZero Nc] :
    SUNLieCoord Nc →ₗ[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ where
  toFun X := ((suLieCoordIso Nc).symm X).toMatrix
  map_add' X Y := by
    rw [(suLieCoordIso Nc).symm.map_add]
    rfl
  map_smul' r X := by
    rw [(suLieCoordIso Nc).symm.map_smul]
    rfl

/-- The decoding map is continuous as well. -/
noncomputable def cmp98LieCoordToAmbientCLM (Nc : ℕ) [NeZero Nc] :
    SUNLieCoord Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ :=
  ⟨cmp98LieCoordToAmbientLinearMap Nc,
    (cmp98LieCoordToAmbientLinearMap Nc).continuous_of_finiteDimensional⟩

@[simp] theorem cmp98AmbientToLieCoordCLM_apply_mem
    (X : SuLie Nc) :
    cmp98AmbientToLieCoordCLM Nc X.toMatrix = suLieCoordIso Nc X := by
  change suLieCoordIso Nc
      (cmp98AmbientToSuLieLinearMap Nc X.toMatrix) =
    suLieCoordIso Nc X
  rw [cmp98AmbientToSuLieLinearMap_apply_mem]

@[simp] theorem cmp98LieCoordToAmbientCLM_apply
    (X : SUNLieCoord Nc) :
    cmp98LieCoordToAmbientCLM Nc X =
      ((suLieCoordIso Nc).symm X).toMatrix := by
  unfold cmp98LieCoordToAmbientCLM
  rfl

/-- Exact retraction law on canonical physical coordinates. -/
@[simp] theorem cmp98AmbientToLieCoordCLM_leftInverse
    (X : SUNLieCoord Nc) :
    cmp98AmbientToLieCoordCLM Nc
        (cmp98LieCoordToAmbientCLM Nc X) = X := by
  rw [cmp98LieCoordToAmbientCLM_apply]
  unfold cmp98AmbientToLieCoordCLM cmp98AmbientToLieCoordLinearMap
  change suLieCoordIso Nc
      (cmp98AmbientToSuLieLinearMap Nc
        (((suLieCoordIso Nc).symm X).toMatrix)) = X
  rw [cmp98AmbientToSuLieLinearMap_apply_mem]
  exact (suLieCoordIso Nc).apply_symm_apply X

/-- Exact coretraction law: decoding the projected coordinates gives the
chosen physical projection of an arbitrary ambient matrix. -/
theorem cmp98LieCoordToAmbientCLM_rightInverse_projection
    (Z : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98LieCoordToAmbientCLM Nc
        (cmp98AmbientToLieCoordCLM Nc Z) =
      (cmp98AmbientToSuLieLinearMap Nc Z).toMatrix := by
  rw [cmp98LieCoordToAmbientCLM_apply]
  unfold cmp98AmbientToLieCoordCLM cmp98AmbientToLieCoordLinearMap
  change
    ((suLieCoordIso Nc).symm
      (suLieCoordIso Nc
        (cmp98AmbientToSuLieLinearMap Nc Z))).toMatrix =
      (cmp98AmbientToSuLieLinearMap Nc Z).toMatrix
  rw [(suLieCoordIso Nc).symm_apply_apply]

end

end YangMills.RG
