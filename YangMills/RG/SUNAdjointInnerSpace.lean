/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.SUNAdjointMatrixSubstrate

/-!
# The inner-product packaging of `su(n)` — P4-ADJ brick 2a
(`hRpoly` campaign — plan §3ter P4-ADJ; brick 1 = Addendum 486)

The `706ffc81` dictamen listed the unpackaged state of brick 1 as the
natural next piece: the trace form and the adjoint action were proved as
raw lemmas, not as instances.  This brick packages them:

* **`SuLie n`** — a type synonym for `↥(suMatrixSubmodule n)` (the synonym
  avoids registering norm instances on the bare submodule subtype, where
  they could collide with ambient matrix-norm choices);
* **`InnerProductSpace ℝ (SuLie n)`** — the trace form as a genuine inner
  product, through `PreInnerProductSpace.Core` + `definite` (all five Core
  fields discharged by the brick-1 lemmas; `suLie_inner_def` anchors the
  definitional identity `⟪X, Y⟫ = matrixTraceInner X.1 Y.1`);
* **`suAdActLin g : SuLie n →ₗ[ℝ] SuLie n`** — the adjoint action packaged
  as a linear map on the subtype (well-definedness from `suAdAct_mem`),
  with `inner_suAdActLin` (inner-product preservation) and
  `norm_suAdActLin` (norm preservation — the packaged form of
  orthogonality), and the action laws `suAdActLin_one`, `suAdActLin_mul`.

**Honest scope.**  Packaging only: `finrank ℝ (SuLie n) = n²−1` (brick 2b,
the hard dimension computation) and the isometric transport to
`SUNLieCoord n` producing a `SUNAdjointModel` instance (brick 3) remain
open.  The Lie bracket/`LieSubalgebra` presentation is not needed for the
model and is not attempted.  Not the interacting Hessian, not `hRpoly`,
not mass gap, not Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix

variable {n : ℕ}

/-- Type synonym for the `su(n)` submodule carrier, receiving the trace-form
norm and inner-product instances. -/
def SuLie (n : ℕ) := ↥(suMatrixSubmodule n)

noncomputable instance : AddCommGroup (SuLie n) :=
  inferInstanceAs (AddCommGroup ↥(suMatrixSubmodule n))

noncomputable instance : Module ℝ (SuLie n) :=
  inferInstanceAs (Module ℝ ↥(suMatrixSubmodule n))

/-- The underlying matrix of an `su(n)` element. -/
def SuLie.toMatrix (X : SuLie n) : Matrix (Fin n) (Fin n) ℂ :=
  (X : ↥(suMatrixSubmodule n)).1

/-- The pre-inner-product core: the trace form on `su(n)`. -/
@[implicit_reducible]
noncomputable def suPreInnerCore (n : ℕ) :
    PreInnerProductSpace.Core ℝ (SuLie n) where
  inner X Y := matrixTraceInner X.toMatrix Y.toMatrix
  conj_inner_symm X Y := by
    simp only [starRingEnd_apply, star_trivial]
    exact matrixTraceInner_comm _ _
  re_inner_nonneg X := matrixTraceInner_self_nonneg _
  add_left X Y Z := matrixTraceInner_add_left _ _ _
  smul_left X Y r := by
    simp only [starRingEnd_apply, star_trivial]
    exact matrixTraceInner_smul_left r _ _

/-- The full inner-product core: the trace form is definite. -/
@[implicit_reducible]
noncomputable def suInnerCore (n : ℕ) :
    InnerProductSpace.Core ℝ (SuLie n) :=
  { __ := suPreInnerCore n
    definite := fun _X hX =>
      Subtype.ext ((matrixTraceInner_self_eq_zero_iff _).mp hX) }

noncomputable instance : NormedAddCommGroup (SuLie n) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _ (suInnerCore n)

noncomputable instance : InnerProductSpace ℝ (SuLie n) :=
  InnerProductSpace.ofCore (suPreInnerCore n)

/-- The inner product of `SuLie n` IS the trace form (definitional anchor). -/
theorem suLie_inner_def (X Y : SuLie n) :
    (inner ℝ X Y : ℝ) = matrixTraceInner X.toMatrix Y.toMatrix := rfl

/-! ## The adjoint action, packaged -/

/-- The adjoint action as a real-linear map on `su(n)`. -/
noncomputable def suAdActLin (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    SuLie n →ₗ[ℝ] SuLie n where
  toFun X := (⟨suAdAct g X.toMatrix, suAdAct_mem g (X : ↥(suMatrixSubmodule n)).2⟩ :
    ↥(suMatrixSubmodule n))
  map_add' X Y := Subtype.ext (suAdAct_add g X.toMatrix Y.toMatrix)
  map_smul' r X := Subtype.ext (suAdAct_smul g r X.toMatrix)

/-- The packaged action agrees with the raw action on matrices. -/
theorem suAdActLin_toMatrix (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X : SuLie n) :
    (suAdActLin g X).toMatrix = suAdAct g X.toMatrix := rfl

/-- **Inner-product preservation** of the packaged adjoint action. -/
theorem inner_suAdActLin (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X Y : SuLie n) :
    (inner ℝ (suAdActLin g X) (suAdActLin g Y) : ℝ) = inner ℝ X Y :=
  matrixTraceInner_suAdAct g X.toMatrix Y.toMatrix

/-- **Norm preservation** of the packaged adjoint action. -/
theorem norm_suAdActLin (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X : SuLie n) :
    ‖suAdActLin g X‖ = ‖X‖ := by
  have h : (inner ℝ (suAdActLin g X) (suAdActLin g X) : ℝ) = inner ℝ X X :=
    inner_suAdActLin g X X
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  calc ‖suAdActLin g X‖
      = Real.sqrt (‖suAdActLin g X‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖X‖ ^ 2) := by rw [h]
    _ = ‖X‖ := Real.sqrt_sq (norm_nonneg _)

/-- The packaged action of the identity. -/
theorem suAdActLin_one :
    suAdActLin (1 : Matrix.specialUnitaryGroup (Fin n) ℂ) =
      LinearMap.id (R := ℝ) (M := SuLie n) := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact suAdAct_one X.toMatrix

/-- The packaged action is multiplicative. -/
theorem suAdActLin_mul (g h : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    suAdActLin (g * h) = (suAdActLin g).comp (suAdActLin (n := n) h) := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact suAdAct_mul g h X.toMatrix

end YangMills.RG
