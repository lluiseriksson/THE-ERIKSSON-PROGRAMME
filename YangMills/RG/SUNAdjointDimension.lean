/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.SUNAdjointInnerSpace

/-!
# The dimension of `su(n)` — P4-ADJ brick 2b
(`hRpoly` campaign — plan §3ter P4-ADJ; bricks 1, 2a = Addenda 486, 488)

THE HARD PIECE of the adjoint-model ladder, named as the next blocker by
the `706ffc81` and `9c173f5a` dictamenes:

`finrank ℝ (SuLie n) = n² − 1`.

Route (self-contained, no basis enumeration):

1. **Hermitian/skew-Hermitian decomposition** — `matrixSelfSkewEquiv`:
   `Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] self × skew` via
   `A ↦ ((A + Aᴴ)/2, (A − Aᴴ)/2)`;
2. **Multiplication by `i`** — `selfSkewMulIEquiv : self ≃ₗ[ℝ] skew`;
3. with `finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2n²`
   (`finrank_real_of_complex` + `finrank_matrix`), (1)+(2) give
   `finrank ℝ skew = n²` (`finrank_skewMatrixSubmodule`);
4. **the imaginary-trace functional** `skewTraceIm : skew →ₗ[ℝ] ℝ`,
   SURJECTIVE for `n ≥ 1` (explicit witness `i·𝟙`, trace `i·n`), and
   `su(n) ≃ₗ[ℝ] ker skewTraceIm` (`suLieEquivKerTraceIm` — on the skew
   subspace the trace is purely imaginary, so `tr = 0 ⟺ im tr = 0`);
5. **rank–nullity** closes: `finrank ℝ (SuLie n) = n² − 1`
   (`finrank_suLie`).

**Honest scope.**  Dimension only: the isometric transport to
`SUNLieCoord n = EuclideanSpace ℝ (Fin (n²−1))` and the `SUNAdjointModel`
instance are brick 3.  Not the interacting Hessian, not `hRpoly`, not
mass gap, not Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

variable {n : ℕ}

/-! ## The Hermitian and skew-Hermitian real submodules -/

/-- Hermitian matrices as a real submodule. -/
def selfMatrixSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᴴ = A}
  add_mem' := by
    rintro A B (ha : _ = _) (hb : _ = _)
    show (A + B)ᴴ = A + B
    rw [conjTranspose_add, ha, hb]
  zero_mem' := by
    show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 0
    simp
  smul_mem' := by
    rintro r A (h : _ = _)
    show (r • A)ᴴ = r • A
    rw [conjTranspose_smul, star_trivial, h]

/-- Skew-Hermitian matrices as a real submodule. -/
def skewMatrixSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᴴ = -A}
  add_mem' := by
    rintro A B (ha : _ = _) (hb : _ = _)
    show (A + B)ᴴ = -(A + B)
    rw [conjTranspose_add, ha, hb, neg_add]
  zero_mem' := by
    show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -0
    simp
  smul_mem' := by
    rintro r A (h : _ = _)
    show (r • A)ᴴ = -(r • A)
    rw [conjTranspose_smul, star_trivial, h]
    module

/-! ## The two structural equivalences -/

/-- The Hermitian/skew-Hermitian decomposition of a complex matrix, as a
real-linear equivalence. -/
noncomputable def matrixSelfSkewEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ]
      ↥(selfMatrixSubmodule n) × ↥(skewMatrixSubmodule n) where
  toFun A :=
    (⟨(1 / 2 : ℝ) • (A + Aᴴ), by
        show ((1 / 2 : ℝ) • (A + Aᴴ))ᴴ = (1 / 2 : ℝ) • (A + Aᴴ)
        rw [conjTranspose_smul, star_trivial, conjTranspose_add,
          conjTranspose_conjTranspose, add_comm]⟩,
     ⟨(1 / 2 : ℝ) • (A - Aᴴ), by
        show ((1 / 2 : ℝ) • (A - Aᴴ))ᴴ = -((1 / 2 : ℝ) • (A - Aᴴ))
        rw [conjTranspose_smul, star_trivial, conjTranspose_sub,
          conjTranspose_conjTranspose]
        module⟩)
  map_add' A B := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (1 / 2 : ℝ) • ((A + B) + (A + B)ᴴ)
        = (1 / 2 : ℝ) • (A + Aᴴ) + (1 / 2 : ℝ) • (B + Bᴴ)
      rw [conjTranspose_add]
      module
    · show (1 / 2 : ℝ) • ((A + B) - (A + B)ᴴ)
        = (1 / 2 : ℝ) • (A - Aᴴ) + (1 / 2 : ℝ) • (B - Bᴴ)
      rw [conjTranspose_add]
      module
  map_smul' r A := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (1 / 2 : ℝ) • ((r • A) + (r • A)ᴴ)
        = r • ((1 / 2 : ℝ) • (A + Aᴴ))
      rw [conjTranspose_smul, star_trivial]
      module
    · show (1 / 2 : ℝ) • ((r • A) - (r • A)ᴴ)
        = r • ((1 / 2 : ℝ) • (A - Aᴴ))
      rw [conjTranspose_smul, star_trivial]
      module
  invFun P := P.1.1 + P.2.1
  left_inv A := by
    show (1 / 2 : ℝ) • (A + Aᴴ) + (1 / 2 : ℝ) • (A - Aᴴ) = A
    module
  right_inv P := by
    obtain ⟨⟨S, hS⟩, ⟨K, hK⟩⟩ := P
    have hS' : Sᴴ = S := hS
    have hK' : Kᴴ = -K := hK
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (1 / 2 : ℝ) • ((S + K) + (S + K)ᴴ) = S
      rw [conjTranspose_add, hS', hK']
      module
    · show (1 / 2 : ℝ) • ((S + K) - (S + K)ᴴ) = K
      rw [conjTranspose_add, hS', hK']
      module

/-- Multiplication by `i` carries Hermitian to skew-Hermitian matrices,
real-linearly and bijectively. -/
noncomputable def selfSkewMulIEquiv (n : ℕ) :
    ↥(selfMatrixSubmodule n) ≃ₗ[ℝ] ↥(skewMatrixSubmodule n) where
  toFun S :=
    ⟨Complex.I • S.1, by
      have hS : (S.1)ᴴ = S.1 := S.2
      show (Complex.I • S.1)ᴴ = -(Complex.I • S.1)
      rw [conjTranspose_smul, Complex.star_def, Complex.conj_I, hS, neg_smul]⟩
  map_add' S T := Subtype.ext (by
    show Complex.I • (S.1 + T.1) = Complex.I • S.1 + Complex.I • T.1
    ext i j
    simp [Matrix.add_apply]
    ring)
  map_smul' r S := Subtype.ext (by
    show Complex.I • (r • S.1) = r • (Complex.I • S.1)
    ext i j
    simp [Complex.real_smul]
    ring)
  invFun K :=
    ⟨(-Complex.I) • K.1, by
      have hK : (K.1)ᴴ = -K.1 := K.2
      show ((-Complex.I) • K.1)ᴴ = (-Complex.I) • K.1
      rw [conjTranspose_smul, Complex.star_def, map_neg, Complex.conj_I,
        neg_neg, hK, smul_neg, neg_smul]⟩
  left_inv S := Subtype.ext (by
    show (-Complex.I) • (Complex.I • S.1) = S.1
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul])
  right_inv K := Subtype.ext (by
    show Complex.I • ((-Complex.I) • K.1) = K.1
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul])

/-! ## The dimension of the skew-Hermitian subspace -/

instance (n : ℕ) : FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  Module.Finite.matrix

instance (n : ℕ) : Module.Finite ℝ ↥(selfMatrixSubmodule n) :=
  Module.Finite.of_surjective
    ((LinearMap.fst ℝ ↥(selfMatrixSubmodule n) ↥(skewMatrixSubmodule n)).comp
      (matrixSelfSkewEquiv n).toLinearMap)
    (fun S => ⟨(matrixSelfSkewEquiv n).symm (S, 0), by
      simp [LinearEquiv.apply_symm_apply]⟩)

instance (n : ℕ) : Module.Finite ℝ ↥(skewMatrixSubmodule n) :=
  Module.Finite.of_surjective
    ((LinearMap.snd ℝ ↥(selfMatrixSubmodule n) ↥(skewMatrixSubmodule n)).comp
      (matrixSelfSkewEquiv n).toLinearMap)
    (fun K => ⟨(matrixSelfSkewEquiv n).symm (0, K), by
      simp [LinearEquiv.apply_symm_apply]⟩)

/-- The real dimension of the ambient complex matrix space (computed with
the DIRECT matrix module instance, via the entry-module-generalized
`Module.finrank_matrix`). -/
theorem finrank_matrix_complex_real (n : ℕ) :
    finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * (n * n) := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp only [Fintype.card_fin]
  ring

/-- **The real dimension of the skew-Hermitian matrices is `n²`.** -/
theorem finrank_skewMatrixSubmodule (n : ℕ) :
    finrank ℝ ↥(skewMatrixSubmodule n) = n * n := by
  have hsum := (matrixSelfSkewEquiv n).finrank_eq
  rw [Module.finrank_prod, finrank_matrix_complex_real] at hsum
  have heq := (selfSkewMulIEquiv n).finrank_eq
  omega

/-! ## The imaginary-trace functional and its kernel -/

/-- The imaginary part of the trace, as a real-linear functional on the
skew-Hermitian matrices — assembled by COMPOSITION of existing linear maps
(no smul-instance pattern matching anywhere). -/
noncomputable def skewTraceIm (n : ℕ) :
    ↥(skewMatrixSubmodule n) →ₗ[ℝ] ℝ :=
  Complex.imLm.comp ((Matrix.traceLinearMap (Fin n) ℝ ℂ).comp
    (skewMatrixSubmodule n).subtype)

/-- Application anchor for the imaginary-trace functional. -/
theorem skewTraceIm_apply (K : ↥(skewMatrixSubmodule n)) :
    skewTraceIm n K = ((K.1).trace).im := rfl

/-- The imaginary-trace functional is surjective for `n ≥ 1`
(explicit witness: real multiples of `i·𝟙`). -/
theorem skewTraceIm_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (skewTraceIm n) := by
  intro r
  have hmem : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈
      skewMatrixSubmodule n := by
    show (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = _
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_I,
      conjTranspose_one, neg_smul]
  set K0 : ↥(skewMatrixSubmodule n) :=
    ⟨Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ), hmem⟩ with hK0
  have hval : skewTraceIm n K0 = (n : ℝ) := by
    show ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)).trace).im = (n : ℝ)
    rw [trace_smul, trace_one]
    simp [Complex.mul_im]
  have hn : ((n : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine ⟨(r / (n : ℝ)) • K0, ?_⟩
  rw [map_smul, hval, smul_eq_mul]
  field_simp

/-- `su(n)` is exactly the kernel of the imaginary-trace functional on the
skew-Hermitian matrices (on skew matrices the trace is purely imaginary). -/
noncomputable def suLieEquivKerTraceIm (n : ℕ) :
    SuLie n ≃ₗ[ℝ] ↥(LinearMap.ker (skewTraceIm n)) where
  toFun X :=
    ⟨⟨X.toMatrix, X.2.1⟩, by
      rw [LinearMap.mem_ker]
      show ((X.toMatrix).trace).im = 0
      have htr : (X.toMatrix).trace = 0 := X.2.2
      rw [htr]
      simp⟩
  map_add' X Y := Subtype.ext (Subtype.ext rfl)
  map_smul' r X := Subtype.ext (Subtype.ext rfl)
  invFun Y :=
    ⟨Y.1.1, by
      have hskew : (Y.1.1)ᴴ = -Y.1.1 := Y.1.2
      have him : ((Y.1.1).trace).im = 0 := Y.2
      have hre : ((Y.1.1).trace).re = 0 := by
        have h1 : ((Y.1.1)ᴴ).trace = star ((Y.1.1).trace) :=
          trace_conjTranspose _
        rw [hskew, trace_neg] at h1
        have h2 : ((Y.1.1).trace).re = -((Y.1.1).trace).re := by
          have := congrArg Complex.re h1
          simpa [Complex.neg_re] using this.symm
        linarith
      refine ⟨hskew, ?_⟩
      apply Complex.ext
      · simpa using hre
      · simpa using him⟩
  left_inv X := Subtype.ext rfl
  right_inv Y := Subtype.ext (Subtype.ext rfl)

/-! ## The dimension theorem -/

/-- **The real dimension of `su(n)` is `n² − 1`** (P4-ADJ brick 2b). -/
theorem finrank_suLie (n : ℕ) [NeZero n] :
    finrank ℝ (SuLie n) = n ^ 2 - 1 := by
  have hrn := (skewTraceIm n).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (skewTraceIm n) = ⊤ :=
    LinearMap.range_eq_top.mpr (skewTraceIm_surjective n)
  rw [hrange, finrank_top, finrank_self, finrank_skewMatrixSubmodule] at hrn
  have hker : finrank ℝ ↥(LinearMap.ker (skewTraceIm n)) = n * n - 1 := by
    omega
  have hequiv := (suLieEquivKerTraceIm n).finrank_eq
  rw [hequiv, hker, pow_two]

end YangMills.RG
