# MATEXP_DET_ONE_DISCHARGE_PROOF.md

**Author**: Cowork agent (Claude)
**Date**: 2026-04-25 (Phase 29)
**Subject**: Concrete Lean proof draft to retire the
`matExp_traceless_det_one` axiom in
`YangMills/Experimental/LieSUN/LieExpCurve.lean`
**Status**: BEST-EFFORT DRAFT — not committed to the project until
verified with a Lean compiler. Once verified, the existing `axiom`
declaration can be replaced with this `theorem`.

---

## 0. Purpose

The Cowork agent has no Lean compiler in its execution environment.
This document provides a complete proof draft that can be
mechanically transcribed into Lean by anyone with build access. The
proof discharges:

```lean
axiom matExp_traceless_det_one
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1
```

into a `theorem` using ONLY existing Mathlib infrastructure as of
the project pin (commit `07642720`).

The key observation: this axiom is for **skew-Hermitian X** (since
the consumer in `lieExpCurve` only invokes it under `hX : Xᴴ = -X`),
and Mathlib has the spectral theorem for Hermitian matrices.

**Important caveat**: the original axiom statement does NOT
require `Xᴴ = -X` in its hypotheses, only `htr : X.trace = 0`. So
the AXIOM is actually CLAIMING something stronger than the
consumer needs — it claims `det(exp(tX)) = 1` for ANY traceless X,
not just skew-Hermitian.

The general claim (Liouville's formula for any traceless X) requires
either:
* The Mathlib `Matrix.det_exp` upstream theorem (TODO in Mathlib),
  OR
* A more delicate argument (e.g., Schur decomposition or analytic
  continuation), which we don't pursue here.

For this discharge, we either:
* **Strengthen the hypothesis** of the axiom to `Xᴴ = -X` (matching
  the actual consumer need), OR
* **Leave the general axiom in place** and prove a specialised
  variant `matExp_skewHerm_traceless_det_one` for the skew-Hermitian
  case, then use the specialised variant in `lieExpCurve`.

We pursue **option B** — leave the original axiom for the general
case (where Mathlib upstream is needed), and add a discharged
specialised variant.

---

## 1. Mathematical proof outline

For skew-Hermitian X (`Xᴴ = -X`) with `tr X = 0`:

### Step 1: Hermitian companion

Define `H := -i • X` (so `X = i • H`).

Verify `H` is Hermitian:
```
Hᴴ = (-i)⋆ • Xᴴ = i • (-X) = -i • X = H
```
where we use `Xᴴ = -X` and `star (-i) = i` (complex conjugate).

### Step 2: Apply spectral theorem

By `Matrix.IsHermitian.spectral_theorem`:
```
H = U · diagonal (RCLike.ofReal ∘ λ) · Uᴴ
```
where `U := H.eigenvectorUnitary` and `λ := H.eigenvalues : n → ℝ`.

### Step 3: Translate to X

Multiply both sides by `i`:
```
X = i • H = U · diagonal (i • RCLike.ofReal ∘ λ) · Uᴴ
        = U · diagonal (fun k => i * (λ k : ℂ)) · Uᴴ
```

### Step 4: Apply exponential

Multiply by `(t : ℂ)`:
```
(t : ℂ) • X = U · diagonal (fun k => t * i * (λ k : ℂ)) · Uᴴ
```

Apply `Matrix.exp_units_conj` (after promoting U to a matrix unit):
```
exp ((t : ℂ) • X) = U · exp (diagonal (fun k => t * i * (λ k : ℂ))) · Uᴴ
```

By `Matrix.exp_diagonal`:
```
exp (diagonal v) = diagonal (NormedSpace.exp ∘ v) for v : n → ℂ
```

So:
```
exp ((t : ℂ) • X) = U · diagonal (fun k => Complex.exp (t * i * (λ k : ℂ))) · Uᴴ
```

### Step 5: Take determinant

```
det (exp ((t : ℂ) • X))
  = det U · det (diagonal (...)) · det Uᴴ
  = det U · ∏_k Complex.exp (t * i * λ k) · det Uᴴ
  = (det U · det Uᴴ) · Complex.exp (∑_k t * i * λ k)
  = (det U · star (det U)) · Complex.exp (t * i * ∑_k λ k)
```

For unitary U: `det U · star (det U) = ‖det U‖² = 1`.

So:
```
det (exp ((t : ℂ) • X)) = Complex.exp (t * i * ∑_k λ k)
```

### Step 6: Use trace condition

`∑_k λ k = tr H` (sum of eigenvalues = trace).
`tr H = tr (-i • X) = -i • tr X = -i • 0 = 0`.

So:
```
det (exp ((t : ℂ) • X)) = Complex.exp (t * i * 0) = Complex.exp 0 = 1
```

QED.

---

## 2. Lean draft

### 2.1 Imports needed

```lean
import Mathlib
-- in particular:
-- Mathlib.Analysis.Normed.Algebra.MatrixExponential  (Matrix.exp_diagonal etc.)
-- Mathlib.Analysis.Matrix.Spectrum                   (IsHermitian.spectral_theorem)
-- Mathlib.LinearAlgebra.Matrix.Determinant.Basic      (det_diagonal, det_mul)
-- Mathlib.LinearAlgebra.UnitaryGroup                  (unitary properties)
```

The existing `LieExpCurve.lean` already imports `Mathlib` (whole), so
all the above are available.

### 2.2 The discharge theorem

```lean
namespace YangMills.Experimental.LieSUN

open scoped Matrix
open Matrix

variable {n : ℕ}

/-- **Discharge** of `matExp_traceless_det_one` for the
    skew-Hermitian case (which is the only consumer-facing case).

    For skew-Hermitian X with tr X = 0, we have det(exp((t:ℂ)·X)) = 1.

    Proof via spectral theorem on the Hermitian companion H = -i·X. -/
theorem matExp_skewHerm_traceless_det_one
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : Xᴴ = -X) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1 := by
  -- Step 1: Define the Hermitian companion H = -i·X.
  set H : Matrix (Fin n) (Fin n) ℂ := (-Complex.I) • X with hH_def
  -- H is Hermitian.
  have hH : H.IsHermitian := by
    show Hᴴ = H
    simp only [hH_def, conjTranspose_smul, hX, smul_neg, neg_smul]
    -- (-i)⋆ • Xᴴ = i • (-X) = -(i • X) = -i • X · (-1) ... hmm let me redo
    -- Goal: ((-i) • X)ᴴ = (-i) • X
    -- LHS = star (-i) • Xᴴ = i • (-X) = -i • X (using i · (-X) = -(i·X) = (-i)·X)
    -- That equals RHS = (-i) • X. ✓
    ring_nf  -- closes by ring on complex scalars
  -- Step 2: Apply spectral theorem to H.
  have h_spec := hH.spectral_theorem
  -- h_spec : H = conjStarAlgAut ℂ _ hH.eigenvectorUnitary
  --                (diagonal (RCLike.ofReal ∘ hH.eigenvalues))
  -- Set U and λ aliases.
  set U := hH.eigenvectorUnitary
  set λ_eig := hH.eigenvalues
  set Dr : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ λ_eig)
  -- Step 3: Translate H = U·Dr·Uᴴ to X = U·(i·Dr)·Uᴴ.
  -- We need exp((t:ℂ)·X) = U · diagonal (fun k => exp(t·i·λ_k)) · Uᴴ.
  -- Use Matrix.exp_units_conj' (which applies after recognising U as a unit).
  have hU_unit : IsUnit (U : Matrix (Fin n) (Fin n) ℂ) :=
    (Matrix.unitaryGroup.toUnits U).isUnit
  -- Step 4: Reduce to det of exp of diagonal.
  -- (t:ℂ)·X = (t:ℂ)·(i·H) = (t·i)·H = (t·i)·(U·Dr·Uᴴ) = U·((t·i)·Dr)·Uᴴ
  -- Hence exp((t:ℂ)·X) = U·exp((t·i)·Dr)·Uᴴ
  --                   = U·diagonal (fun k => exp((t·i)·(λ_eig k : ℂ))) · Uᴴ
  -- And det = det(U·diagonal(...)·Uᴴ)
  --         = det(U) · ∏_k exp((t·i)·λ_eig k) · det(Uᴴ)
  --         = |det U|² · exp(t·i·∑_k λ_eig k)
  --         = 1 · exp(t·i·tr H)
  --         = exp(t·i·(-i·tr X))
  --         = exp(t·tr X)
  --         = exp 0 = 1.
  --
  -- Detailed Lean execution requires careful API navigation; the
  -- mathematical content is fully captured above. This is the place
  -- where a Lean compiler is genuinely needed to iterate.
  sorry  -- remaining ~50 LOC of careful Mathlib API work

end YangMills.Experimental.LieSUN
```

### 2.3 Honest assessment

The proof above is **mathematically complete** but the Lean execution
of Steps 4-5 (the determinant computation) requires:
* Navigating `conjStarAlgAut` (which is the inner automorphism).
* Using `Matrix.exp_units_conj'` carefully.
* Translating between `RCLike.ofReal ∘ λ` (the diagonal entry form) and
  ℂ-valued diagonals.
* Using `Matrix.det_mul`, `Matrix.det_diagonal`, plus the unitarity
  property `det U · star (det U) = 1`.

Each step is standard but the API navigation needs iteration that's
not feasible without a compiler. A user with `lake` access could:
1. Place this draft in
   `YangMills/Experimental/LieSUN/MatExpDetOneProof.lean`.
2. Iterate on the `sorry` until it compiles.
3. Replace the original `axiom matExp_traceless_det_one` with a
   theorem that defers to this proof (under the additional `hX`
   hypothesis).

---

## 3. Consumer-side change

The current consumer in `LieExpCurve.lean`:

```lean
noncomputable def lieExpCurve
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (t : ℝ) :
    ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
  ⟨U.val * matExp ((t : ℂ) • X), by
    ...
           by rw [Matrix.det_mul, ..., matExp_traceless_det_one X htr t, one_mul]⟩⟩
```

Already passes `hX` to `lieExpCurve`. Just change the call site to:
```lean
matExp_skewHerm_traceless_det_one X hX htr t
```

(adding the `hX` argument, which is already in scope).

The original general `matExp_traceless_det_one` axiom can then be
**deleted** since it has only one consumer and that consumer is
satisfied by the specialised version.

---

## 4. Aggregate impact

If this discharge proof is verified and committed:

| Metric | Before | After |
|---|---|---|
| Project axioms (Experimental/) | 14 | **13** |
| `matExp_traceless_det_one` consumers | 1 | 0 |
| `matExp_skewHerm_traceless_det_one` (proven) | n/a | 1 consumer |

The axiom retired moves from "research-level Mathlib gap" to "fully
proven theorem from existing Mathlib infrastructure". This is a
**genuine win** (not just hypothesis-conditioning).

---

## 5. Why I haven't committed this

Without a Lean compiler in my environment, attempting to commit a
proof with sorries (or potentially-broken non-sorry proofs) would
either:
* Add a sorry to the project (reverses Phase 22 sorry-free milestone).
* Risk breaking the project build via incorrect lemma names / API
  mismatches.

The right path: a session with Lean compiler access (Codex daemon
during off-hours, or the user themselves) implements the discharge.
This document provides the complete mathematical content for that
implementation.

---

## 6. Other discharges in the same family

Per `MATHLIB_GAPS_AUDIT.md` Tier A, similar proofs are tractable for:

* SU(N) generator basis (~250 LOC) — explicit construction
* `gronwall_variance_decay` (~150-250 LOC) — Gronwall + variance bridge
* `sunGeneratorData` — bundles previous proofs

I provide the math sketches in the audit document but defer the Lean
implementation pending compiler access.

---

*Discharge proof draft prepared 2026-04-25 by Cowork agent (Phase 29).
This is a structural deliverable: the math is complete, the Lean
execution is queued for a compiler-available session.*

---

## 7. Late-session update — `n = 1` case **closed as a Lean theorem** (2026-04-25 evening, Phase 77)

The `n = 1` base case of the underlying Mathlib TODO
(`Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`)
has been closed as a **Lean theorem**, not an axiom, in:

* `YangMills/Experimental/LieSUN/MatExpDetTraceDimOne.lean` (Phase 77).

The proof uses `Matrix.exp_diagonal` + `Matrix.det_diagonal` +
`Matrix.trace_fin_one` + the fact that every 1×1 matrix is diagonal
(`Subsingleton (Fin 1)`). Two theorems are exposed:

1. `matExp_det_eq_exp_trace_dim_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
   Matrix.det (matExp A) = Complex.exp (Matrix.trace A)` — the
   general identity, restricted to `n = 1`.
2. Its corollary
   `matExp_smul_traceless_det_eq_one_dim_one (A) (htr : trace A = 0)
   (t : ℝ) : det (matExp ((t : ℂ) • A)) = 1` — exactly the `n = 1`
   case of the `matExp_traceless_det_one` axiom statement.

The corollary serves as a **Mathlib-PR fixture**: any future general
proof of the Mathlib TODO must agree with this file at `n = 1`. It
also demonstrates that the discharge pattern (Subsingleton-collapse +
diagonalisation) generalises naturally to the next case via Schur
decomposition.

Combined with `MatExpTracelessDimOne.lean` (Phase 62), the project
now has **two converging Lean theorems** for the `n = 1` case of
`matExp_traceless_det_one`:

| File | Approach | Theorem |
|------|----------|---------|
| `MatExpTracelessDimOne.lean` (Phase 62) | direct: traceless ⇒ A = 0 ⇒ matExp 0 = 1 | `matExp_traceless_det_one_dim_one` |
| `MatExpDetTraceDimOne.lean` (Phase 77) | via general det(exp) = exp(trace) at n=1 | `matExp_smul_traceless_det_eq_one_dim_one` |

The remaining work (for `n ≥ 2`) is the Schur decomposition path
sketched in §3 above. When Mathlib closes the upstream TODO, this
project's axiom can be retired.
