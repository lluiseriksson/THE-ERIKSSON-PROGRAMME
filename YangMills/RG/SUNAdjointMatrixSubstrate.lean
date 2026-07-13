/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib

/-!
# The matricial `su(n)` substrate — P4-ADJ brick 1
(`hRpoly` campaign — plan §3ter P4-ADJ, registered Addendum 477)

The TRUE adjoint model obligation (external finding, ledger Addendum 477):
`SUNAdjointModel` is abstract orthogonal-action data, witnessed so far only
by the NAMED trivial model.  This brick builds the concrete matrix-side
substrate the true model needs:

* **`suMatrixSubmodule n`** — `su(n)` as a REAL submodule of
  `Matrix (Fin n) (Fin n) ℂ`: skew-Hermitian (`Aᴴ = −A`) and traceless,
  with the definitional membership test `mem_suMatrixSubmodule_iff`.
* **`matrixTraceInner X Y := re (tr (Xᴴ·Y))`** — the trace form on the
  ambient matrix space: symmetric (`matrixTraceInner_comm`), real-bilinear
  (`matrixTraceInner_add_left`, `matrixTraceInner_smul_left`), positive
  (`matrixTraceInner_self_nonneg`), and definite
  (`matrixTraceInner_self_eq_zero_iff` — via the PSD trace order on `ℂ`,
  `ComplexOrder` scoped).
* **`suAdAct g X := g·X·gᴴ`** — the adjoint action of
  `Matrix.specialUnitaryGroup (Fin n) ℂ`: it preserves the submodule
  (`suAdAct_mem`), preserves the trace form (`matrixTraceInner_suAdAct` —
  the ORTHOGONALITY that `SUNAdjointModel.ad_inner` demands, at the matrix
  level), and is a real-linear group action (`suAdAct_one`, `suAdAct_mul`,
  `suAdAct_add`, `suAdAct_smul`).

**Honest scope.**  Substrate only: no coordinate identification with
`SUNLieCoord n = EuclideanSpace ℝ (Fin (n²−1))` is made here, no
`finrank ℝ (suMatrixSubmodule n) = n²−1` is computed, and no
`SUNAdjointModel` instance is produced — those are P4-ADJ bricks 2 and 3.
Nothing here touches the flat shell, `hRpoly`, mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-! ## The real submodule `su(n)` -/

/-- `su(n)` as a real submodule of the complex `n × n` matrices:
skew-Hermitian and traceless. -/
def suMatrixSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᴴ = -A ∧ A.trace = 0}
  add_mem' := by
    rintro A B ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    constructor
    · rw [conjTranspose_add, ha1, hb1, neg_add]
    · rw [trace_add, ha2, hb2, add_zero]
  zero_mem' := by
    constructor
    · simp
    · simp
  smul_mem' := by
    rintro r A ⟨h1, h2⟩
    constructor
    · rw [conjTranspose_smul, star_trivial, h1, smul_neg]
    · rw [trace_smul, h2, smul_zero]

/-- Membership test: skew-Hermitian and traceless (definitional). -/
theorem mem_suMatrixSubmodule_iff (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ suMatrixSubmodule n ↔ Aᴴ = -A ∧ A.trace = 0 :=
  Iff.rfl

/-! ## The trace inner form -/

/-- The real trace form `⟨X, Y⟩ = re (tr (Xᴴ · Y))` on complex matrices. -/
noncomputable def matrixTraceInner (X Y : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((Xᴴ * Y).trace).re

/-- Symmetry of the trace form. -/
theorem matrixTraceInner_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceInner X Y = matrixTraceInner Y X := by
  unfold matrixTraceInner
  have h : (Yᴴ * X) = (Xᴴ * Y)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [h, trace_conjTranspose]
  exact (Complex.conj_re _).symm

/-- The trace form is nonnegative on the diagonal (PSD trace order on `ℂ`). -/
theorem matrixTraceInner_self_nonneg (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ matrixTraceInner X X := by
  have hpsd : PosSemidef (Xᴴ * X) := posSemidef_conjTranspose_mul_self X
  have htr : (0 : ℂ) ≤ (Xᴴ * X).trace := hpsd.trace_nonneg
  rw [Complex.le_def] at htr
  simpa using htr.1

/-- Definiteness of the trace form. -/
theorem matrixTraceInner_self_eq_zero_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceInner X X = 0 ↔ X = 0 := by
  constructor
  · intro hre
    unfold matrixTraceInner at hre
    have hpsd : PosSemidef (Xᴴ * X) := posSemidef_conjTranspose_mul_self X
    have htr : (0 : ℂ) ≤ (Xᴴ * X).trace := hpsd.trace_nonneg
    rw [Complex.le_def] at htr
    have hzero : (Xᴴ * X).trace = 0 := by
      apply Complex.ext
      · simpa [Complex.zero_re] using hre
      · simpa [Complex.zero_im] using htr.2.symm
    exact trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
  · intro h
    subst h
    unfold matrixTraceInner
    simp

/-- Real bilinearity, left argument (additivity). -/
theorem matrixTraceInner_add_left (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceInner (X + Y) Z = matrixTraceInner X Z + matrixTraceInner Y Z := by
  unfold matrixTraceInner
  rw [conjTranspose_add, add_mul, trace_add, Complex.add_re]

/-- Real bilinearity, left argument (real scalars). -/
theorem matrixTraceInner_smul_left (r : ℝ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceInner (r • X) Y = r * matrixTraceInner X Y := by
  unfold matrixTraceInner
  have h1 : ((r • X)ᴴ : Matrix (Fin n) (Fin n) ℂ) = r • Xᴴ := by
    rw [conjTranspose_smul, star_trivial]
  have h2 : (r • Xᴴ : Matrix (Fin n) (Fin n) ℂ) * Y = r • (Xᴴ * Y) :=
    smul_mul_assoc r _ _
  have h3 : ((r • (Xᴴ * Y) : Matrix (Fin n) (Fin n) ℂ)).trace
      = r • ((Xᴴ * Y).trace) := trace_smul r _
  rw [h1, h2, h3, Complex.real_smul]
  simp [Complex.mul_re]

/-! ## The adjoint action of the special unitary group -/

/-- The adjoint action `Ad(g) X = g · X · gᴴ` of the special unitary group
on complex matrices (for unitary `g`, `gᴴ = g⁻¹`). -/
noncomputable def suAdAct (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (g : Matrix (Fin n) (Fin n) ℂ) * X * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ

/-- Unitarity, conjugate-transpose-left form: `gᴴ · g = 1`. -/
theorem su_conjTranspose_mul_self (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ) * (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hu : (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have h := Matrix.mem_unitaryGroup_iff'.mp hu
  simpa [Matrix.star_eq_conjTranspose] using h

/-- Unitarity, conjugate-transpose-right form: `g · gᴴ = 1`. -/
theorem su_mul_conjTranspose_self (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    (g : Matrix (Fin n) (Fin n) ℂ) * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ) = 1 := by
  have hu : (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have h := Matrix.mem_unitaryGroup_iff.mp hu
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The conjugate transpose of the adjoint image: `(g X gᴴ)ᴴ = g Xᴴ gᴴ`. -/
theorem suAdAct_conjTranspose (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (suAdAct g X)ᴴ = suAdAct g Xᴴ := by
  unfold suAdAct
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- The adjoint action preserves `su(n)`. -/
theorem suAdAct_mem (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ suMatrixSubmodule n) :
    suAdAct g X ∈ suMatrixSubmodule n := by
  rw [mem_suMatrixSubmodule_iff] at hX ⊢
  obtain ⟨hskew, htr⟩ := hX
  constructor
  · rw [suAdAct_conjTranspose, hskew]
    unfold suAdAct
    rw [Matrix.mul_neg, Matrix.neg_mul]
  · unfold suAdAct
    rw [Matrix.trace_mul_cycle, su_conjTranspose_mul_self,
      Matrix.one_mul, htr]

/-- **Orthogonality of the adjoint action** (the `ad_inner` demand of
`SUNAdjointModel`, at the matrix level): the trace form is invariant. -/
theorem matrixTraceInner_suAdAct (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixTraceInner (suAdAct g X) (suAdAct g Y) = matrixTraceInner X Y := by
  unfold matrixTraceInner
  congr 1
  have hexp : (suAdAct g X)ᴴ * suAdAct g Y
      = suAdAct g (Xᴴ * Y) := by
    rw [suAdAct_conjTranspose]
    unfold suAdAct
    calc (g : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
          (g : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ) * Y *
            (g : Matrix (Fin n) (Fin n) ℂ)ᴴ)
        = (g : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
          (((g : Matrix (Fin n) (Fin n) ℂ)ᴴ *
            (g : Matrix (Fin n) (Fin n) ℂ)) *
              (Y * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ)) := by
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix (Fin n) (Fin n) ℂ) * Xᴴ *
          (Y * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by
          rw [su_conjTranspose_mul_self, Matrix.one_mul]
      _ = (g : Matrix (Fin n) (Fin n) ℂ) * (Xᴴ * Y) *
          (g : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
          simp only [Matrix.mul_assoc]
  rw [hexp]
  unfold suAdAct
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
    su_conjTranspose_mul_self, Matrix.one_mul]

/-- The adjoint action of the identity is the identity. -/
theorem suAdAct_one (X : Matrix (Fin n) (Fin n) ℂ) :
    suAdAct (1 : Matrix.specialUnitaryGroup (Fin n) ℂ) X = X := by
  unfold suAdAct
  simp

/-- The adjoint action is multiplicative: `Ad(g·h) = Ad(g) ∘ Ad(h)`. -/
theorem suAdAct_mul (g h : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    suAdAct (g * h) X = suAdAct g (suAdAct h X) := by
  unfold suAdAct
  have hcoe : ((g * h : Matrix.specialUnitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) =
      (g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hcoe, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The adjoint action is additive in the matrix argument. -/
theorem suAdAct_add (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    suAdAct g (X + Y) = suAdAct g X + suAdAct g Y := by
  unfold suAdAct
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The adjoint action commutes with real scalars. -/
theorem suAdAct_smul (g : Matrix.specialUnitaryGroup (Fin n) ℂ)
    (r : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    suAdAct g (r • X) = r • suAdAct g X := by
  unfold suAdAct
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * (r • X)
      = r • ((g : Matrix (Fin n) (Fin n) ℂ) * X) :=
    mul_smul_comm r _ _
  rw [h1, smul_mul_assoc]

end YangMills.RG
