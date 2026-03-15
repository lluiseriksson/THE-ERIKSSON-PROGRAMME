import Mathlib
import YangMills.Experimental.LieSUN.LieDerivativeDef

/-!
# Experimental: Exponential Curve on SU(N)

Layer B: Concrete instantiation of lieDerivativeVia for SU(N).

Goal: define lieExpCurve N_c X U t = U · exp(t·X) ∈ SU(N)
and prove lieDerivativeVia (lieExpCurve N_c X) is linear/constant.

## Mathlib status for each step

| Step | Mathlib status |
|------|---------------|
| `NormedSpace.exp` for matrices | ✅ available |
| `(exp X)ᴴ = exp(Xᴴ)` via `exp_star` | ✅ likely available |
| `exp(-X) = (exp X)⁻¹` | ✅ `NormedSpace.exp_neg` |
| `U · exp(tX) ∈ U(N)` for Xᴴ=-X | ✅ probable from above |
| `det(exp X) = exp(tr X)` (Jacobi) | ❌ Mathlib TODO |
| `U · exp(tX) ∈ SU(N)` for tr(X)=0 | ❌ needs Jacobi |
| `HasDerivAt (fun t => exp(t·X)) ...` | ⚠️ needs checking |
-/

namespace YangMills.Experimental.LieSUN

open Matrix NormedSpace

variable (N_c : ℕ) [NeZero N_c]

/-! ## Check: what matrix exp exists in Mathlib? -/

-- Test 1: NormedSpace.exp for complex matrices
#check (NormedSpace.exp ℂ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)

-- Test 2: exp_star (conjugate of exp)
#check @NormedSpace.exp_star

-- Test 3: exp_neg
#check @NormedSpace.exp_neg

-- Test 4: HasDerivAt for exp
#check @NormedSpace.hasDerivAt_exp

-- Test 5: specialUnitaryGroup membership
#check Matrix.specialUnitaryGroup
#check Matrix.mem_specialUnitaryGroup_iff

/-! ## The unitary part: exp(tX) ∈ U(N) for Xᴴ = -X -/

/-- For a skew-Hermitian matrix X (Xᴴ = -X),
    the matrix exponential exp(tX) is unitary. -/
theorem exp_skewHermitian_unitary
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp ℂ (t • X))ᴴ * (NormedSpace.exp ℂ (t • X)) = 1 := by
  -- Strategy:
  -- (exp(tX))ᴴ = exp((tX)ᴴ)         [exp_star]
  --            = exp(t · Xᴴ)          [conjTranspose_smul]
  --            = exp(t · (-X))         [hX]
  --            = exp(-(tX))            [smul_neg]
  --            = (exp(tX))⁻¹           [exp_neg]
  -- Therefore (exp tX)ᴴ · (exp tX) = (exp tX)⁻¹ · (exp tX) = 1
  sorry

/-- For a traceless skew-Hermitian matrix X,
    det(exp(tX)) = 1.
    BLOCKED: requires det(exp A) = exp(tr A) (Jacobi's formula).
    This is a known Mathlib TODO. -/
theorem exp_traceless_det_one
    (X : Matrix (Fin N_c) (Fin N_c) ℂ)
    (hX : Xᴴ = -X) (htr : X.trace = 0) (t : ℝ) :
    (NormedSpace.exp ℂ (t • X)).det = 1 := by
  -- det(exp(tX)) = exp(tr(tX)) = exp(t · tr(X)) = exp(0) = 1
  -- MISSING: Matrix.det_exp or equivalent
  sorry

/-! ## Attempt: prove unitary part from Mathlib -/

/-- Attempt to prove exp_skewHermitian_unitary without sorry.
    This checks which Mathlib lemmas are actually available. -/
theorem exp_skewHermitian_unitary_attempt
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp ℂ (t • X))ᴴ * (NormedSpace.exp ℂ (t • X)) = 1 := by
  have h1 : (NormedSpace.exp ℂ (t • X))ᴴ = NormedSpace.exp ℂ ((t • X)ᴴ) := by
    rw [NormedSpace.exp_star]
  have h2 : (t • X)ᴴ = -(t • X) := by
    rw [conjTranspose_smul, hX]
    simp [conjTranspose_neg, smul_neg]
  have h3 : NormedSpace.exp ℂ (-(t • X)) = (NormedSpace.exp ℂ (t • X))⁻¹ := by
    exact (NormedSpace.exp_neg ℂ (t • X)).symm
  rw [h1, h2, h3]
  exact mul_inv_cancel₀ (NormedSpace.exp_ne_zero ℂ _)

/-! ## What compiles tells us the exact gap -/

end YangMills.Experimental.LieSUN
