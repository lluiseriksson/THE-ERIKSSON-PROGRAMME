import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# LieDerivative Roadmap — Future formalization plan

## Current status

The three `lieDerivative_*` axioms in `SUN_DirichletForm.lean` are the most
attackable of the 7 remaining axioms in the Eriksson Programme.

They are currently axioms only because `SU(N)` as
`Matrix.specialUnitaryGroup (Fin N) ℂ` does NOT yet have a `LieGroup` instance
in Mathlib (requires `ModelWithCorners` + `ChartedSpace` + `ContMDiff`).

## Desired definition

Once Mathlib supports `SU(N)` as a smooth manifold, replace `opaque lieDerivative`
with this concrete definition:
```lean
-- The one-parameter curve through U in direction Xᵢ:
--   γ_{i,U}(t) = U · exp(t · Xᵢ)  ∈ SU(N)
noncomputable def lieExpCurve (N_c : ℕ) (i : LieGenIndex N_c)
    (U : SUN_State_Concrete N_c) (t : ℝ) : SUN_State_Concrete N_c :=
  ... -- needs Matrix.exp + proof that U·exp(tXᵢ) ∈ SU(N)

-- The Lie derivative: ordinary derivative of f along the curve
noncomputable def lieDerivative (N_c : ℕ) (i : LieGenIndex N_c)
    (f : SUN_State_Concrete N_c → ℝ) (U : SUN_State_Concrete N_c) : ℝ :=
  deriv (fun t : ℝ => f (lieExpCurve N_c i U t)) 0
```

## Three target theorems (currently axioms)

With the `lieExpCurve` definition above, the three axioms become theorems:

### lieDerivative_const_add
```lean
theorem lieDerivative_const_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f : SUN_State_Concrete N_c → ℝ) (c : ℝ)
    (hf : DifferentiableAt ℝ (fun t => f (lieExpCurve N_c i · t)) 0) :
    lieDerivative N_c i (fun U => f U + c) = lieDerivative N_c i f := by
  ext U
  simp only [lieDerivative]
  -- deriv (fun t => f(γ(t)) + c) 0 = deriv (fun t => f(γ(t))) 0
  have := deriv_add (hf U) (differentiableAt_const c)
  simp [deriv_const] at this
  exact this
```
Key Mathlib lemma: `deriv_const_add` or `deriv_add` + `deriv_const`.

### lieDerivative_smul
```lean
theorem lieDerivative_smul (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) (f : SUN_State_Concrete N_c → ℝ)
    (hf : ∀ U, DifferentiableAt ℝ (fun t => f (lieExpCurve N_c i U t)) 0) :
    lieDerivative N_c i (fun U => c * f U) = fun U => c * lieDerivative N_c i f U := by
  ext U
  simp only [lieDerivative]
  -- deriv (fun t => c * f(γ(t))) 0 = c * deriv (fun t => f(γ(t))) 0
  exact deriv_const_mul c (hf U)
```
Key Mathlib lemma: `deriv_const_mul`.

### lieDerivative_add
```lean
theorem lieDerivative_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f g : SUN_State_Concrete N_c → ℝ)
    (hf : ∀ U, DifferentiableAt ℝ (fun t => f (lieExpCurve N_c i U t)) 0)
    (hg : ∀ U, DifferentiableAt ℝ (fun t => g (lieExpCurve N_c i U t)) 0) :
    lieDerivative N_c i (f + g) = lieDerivative N_c i f + lieDerivative N_c i g := by
  ext U
  simp only [lieDerivative, Pi.add_apply]
  -- deriv (fun t => f(γ(t)) + g(γ(t))) 0
  --   = deriv (fun t => f(γ(t))) 0 + deriv (fun t => g(γ(t))) 0
  exact deriv_add (hf U) (hg U)
```
Key Mathlib lemma: `deriv_add`.

## Mathlib blockers

To instantiate `lieExpCurve` concretely, we need:

1. **`Matrix.exp`** for `Matrix (Fin N) (Fin N) ℂ`
   - Status: `Matrix.exp` exists in Mathlib as `NormedSpace.exp`
   - But: need proof that `U · exp(t·Xᵢ) ∈ specialUnitaryGroup`

2. **`specialUnitaryGroup` is closed under `exp`**
   - Proof: if `A ∈ su(N)` (skew-Hermitian, trace-free), then `exp(tA) ∈ SU(N)`
   - This follows from `Matrix.exp_mem_unitaryGroup` (if it exists) or needs proof

3. **`DifferentiableAt` for `t ↦ exp(t·Xᵢ)·U`**
   - `Matrix.exp` is smooth → composition is smooth
   - Mathlib likely has this but needs `HasDerivAt (fun t => Matrix.exp (t • X)) ...`

## Immediate check: does Matrix.exp exist?
```lean
#check Matrix.exp  -- might be NormedSpace.exp applied to matrices
#check unitaryGroup  -- related structure
```

## Summary

| What | Status |
|------|--------|
| `deriv_add`, `deriv_const_mul` | ✅ In Mathlib |
| `DifferentiableAt` for smooth functions | ✅ In Mathlib |
| `Matrix.exp` for `M_N(ℂ)` | ⚠️ Check `NormedSpace.exp` |
| `exp(tX) ∈ SU(N)` for `X ∈ su(N)` | ❓ May need proof |
| `LieGroup` instance for `SU(N)` | ❌ Not yet in Mathlib |

**Estimated effort to close all 3 axioms once blockers resolved**: ~1 session.
-/

namespace YangMills

-- Placeholder: verify Matrix.exp availability
section MatrixExpCheck

-- In Mathlib, matrix exponential is via NormedSpace.exp
-- #check NormedSpace.exp  -- the general exp in a Banach algebra
-- For matrices: exp A = Σ Aⁿ/n!

end MatrixExpCheck

end YangMills
