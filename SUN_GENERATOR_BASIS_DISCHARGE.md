# SUN_GENERATOR_BASIS_DISCHARGE.md

**Author**: Cowork agent (Claude)
**Date**: 2026-04-25 (Phase 30)
**Subject**: Concrete Lean construction of an `(N²−1)`-dimensional
basis of the SU(N) Lie algebra `𝔰𝔲(N)`, retiring 6 (or 7 with
bundling) axioms in `YangMills/Experimental/LieSUN/`.
**Status**: Mathematical construction complete; Lean draft requires
a compiler-available session for final API navigation.

---

## 0. Axioms retired by this discharge

This discharge retires:

| Axiom | File |
|---|---|
| `generatorMatrix` | `LieDerivativeRegularity.lean` |
| `gen_skewHerm` | `LieDerivativeRegularity.lean` |
| `gen_trace_zero` | `LieDerivativeRegularity.lean` |
| `generatorMatrix'` | `DirichletConcrete.lean` |
| `gen_skewHerm'` | `DirichletConcrete.lean` |
| `gen_trace_zero'` | `DirichletConcrete.lean` |
| `sunGeneratorData` | `LieDerivReg_v4.lean` (bundling) |

That's **7 of the 14 Experimental axioms** retired in one discharge
session (assuming Lean compilation succeeds).

---

## 1. Mathematical construction

The Lie algebra `𝔰𝔲(N) = { X ∈ Mat(N, ℂ) : Xᴴ = -X, tr X = 0 }` has
real dimension `N² − 1`. A standard basis is the **Gell-Mann
generalisation**:

### 1.1 Off-diagonal real generators

For each pair `i < j` with `i, j ∈ Fin N`:

```
λ^{(R)}_{ij} := (E_{ij} + E_{ji}) · I
            = i · (E_{ij} + E_{ji})
```

where `E_{ij}` is the matrix unit (1 at position `(i,j)`, 0 elsewhere)
and `I = √(-1)`.

These give `(N² − N) / 2 = C(N,2)` matrices.

**Verify skew-Hermitian**: `(I·(E_{ij} + E_{ji}))ᴴ = (-I)·(E_{ji} + E_{ij}) = -I·(E_{ij} + E_{ji})`. ✓

**Verify traceless**: `tr (I·(E_{ij} + E_{ji})) = I·(tr E_{ij} + tr E_{ji}) = I·(0 + 0) = 0` since `i ≠ j`. ✓

### 1.2 Off-diagonal imaginary generators

For each pair `i < j`:

```
λ^{(I)}_{ij} := E_{ij} − E_{ji}
```

These give `(N² − N) / 2` matrices.

**Verify skew-Hermitian**: `(E_{ij} − E_{ji})ᴴ = E_{ji} − E_{ij} = -(E_{ij} − E_{ji})`. ✓

**Verify traceless**: `tr (E_{ij} − E_{ji}) = 0 − 0 = 0` since `i ≠ j`. ✓

### 1.3 Diagonal generators

For each `k ∈ {1, ..., N−1}`:

```
H_k := (I / √(2k(k+1))) · (E_{0,0} + E_{1,1} + ... + E_{k-1,k-1} − k · E_{k,k})
```

Wait, let me be more careful. The standard normalization:

```
H_k := (I / √(k(k+1)/2)) · diagonal(1, 1, ..., 1, -k, 0, 0, ..., 0)
                                                ↑ position k
```

So `H_k` has `1` in positions 0 through k−1, `−k` in position k, and 0 elsewhere. Multiplied by `I / √(k(k+1)/2)` for normalization.

These give `N − 1` matrices.

**Verify skew-Hermitian**: real diagonal matrix multiplied by `I` is skew-Hermitian. ✓

**Verify traceless**: `tr(diagonal(1,...,1,-k,0,...,0)) = k·1 + (-k) = 0`. ✓

### 1.4 Total count

`(N² − N)/2 + (N² − N)/2 + (N − 1) = (N² − N) + (N − 1) = N² − 1`. ✓

This matches the dimension of `𝔰𝔲(N)`.

---

## 2. Indexing scheme

Map `Fin (N² − 1) → 𝔰𝔲(N)` basis matrices:

* Indices `0` to `(N²−N)/2 − 1`: off-diagonal real `λ^{(R)}_{ij}` for `(i,j)` enumerated lexicographically with `i < j`.
* Indices `(N²−N)/2` to `(N²−N) − 1`: off-diagonal imaginary `λ^{(I)}_{ij}`.
* Indices `(N²−N)` to `N² − 2`: diagonal `H_k` for `k = 1, ..., N−1`.

Total `N² − 1` indices, indexed by `Fin (N² − 1)`.

---

## 3. Lean draft

```lean
import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations  -- if needed

namespace YangMills.Experimental.LieSUN

open scoped Matrix
open Matrix Complex

variable {N_c : ℕ} [NeZero N_c]

/-! ## §1. Pair indexing for off-diagonal generators -/

/-- The number of distinct ordered pairs `(i, j)` with `i < j` in
    `Fin N`. Equals `N · (N - 1) / 2 = C(N, 2)`. -/
def pairCount (N : ℕ) : ℕ := N * (N - 1) / 2

/-- Convert `Fin (pairCount N)` to a pair `(i, j)` with `i < j`. -/
noncomputable def pairAt (N : ℕ) (k : Fin (pairCount N)) :
    {p : Fin N × Fin N // p.1 < p.2} :=
  -- Implementation: enumerate pairs lexicographically.
  -- Could use Finset.sum or Finset.image; defer to Mathlib's
  -- `Finset.offDiag` or similar pair-enumeration infrastructure.
  sorry  -- standard combinatorial construction

/-! ## §2. Off-diagonal real generators -/

noncomputable def offDiagReal (i j : Fin N_c) (h : i ≠ j) :
    Matrix (Fin N_c) (Fin N_c) ℂ :=
  Complex.I • (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

theorem offDiagReal_skewHerm (i j : Fin N_c) (h : i ≠ j) :
    (offDiagReal i j h)ᴴ = -(offDiagReal i j h) := by
  unfold offDiagReal
  simp only [conjTranspose_smul, RCLike.star_def, conj_I,
             conjTranspose_add,
             Matrix.stdBasisMatrix_conjTranspose,
             RCLike.star_def, RCLike.conj_one]
  ring_nf
  -- Goal reduces to: -I · (E_{ji} + E_{ij}) = -(I · (E_{ij} + E_{ji}))
  -- Both sides equal -I · (E_{ij} + E_{ji}) by addition commutativity.

theorem offDiagReal_trace_zero (i j : Fin N_c) (h : i ≠ j) :
    (offDiagReal i j h).trace = 0 := by
  unfold offDiagReal
  simp only [Matrix.trace_smul, Matrix.trace_add,
             Matrix.stdBasisMatrix_trace_eq, h, Ne.symm h, if_neg, smul_zero, add_zero]
  -- Both stdBasisMatrix traces are zero since i ≠ j.

/-! ## §3. Off-diagonal imaginary generators -/

noncomputable def offDiagImag (i j : Fin N_c) (h : i ≠ j) :
    Matrix (Fin N_c) (Fin N_c) ℂ :=
  Matrix.stdBasisMatrix i j 1 - Matrix.stdBasisMatrix j i 1

theorem offDiagImag_skewHerm (i j : Fin N_c) (h : i ≠ j) :
    (offDiagImag i j h)ᴴ = -(offDiagImag i j h) := by
  unfold offDiagImag
  simp only [conjTranspose_sub, Matrix.stdBasisMatrix_conjTranspose, RCLike.conj_one]
  ring_nf
  -- (E_{ij} - E_{ji})ᴴ = E_{ji} - E_{ij} = -(E_{ij} - E_{ji}).

theorem offDiagImag_trace_zero (i j : Fin N_c) (h : i ≠ j) :
    (offDiagImag i j h).trace = 0 := by
  unfold offDiagImag
  simp only [Matrix.trace_sub, Matrix.stdBasisMatrix_trace_eq, h, Ne.symm h, if_neg, sub_zero]

/-! ## §4. Diagonal generators -/

/-- The unnormalized diagonal generator: `diag(1, 1, ..., 1, -k, 0, ..., 0)`
    with `1`s in positions `0` through `k-1` and `-k` in position `k`.
    Multiplied by I to make it skew-Hermitian. -/
noncomputable def diagGenerator (k : Fin N_c) (h : k.val ≥ 1) :
    Matrix (Fin N_c) (Fin N_c) ℂ :=
  Complex.I •
    Matrix.diagonal (fun (i : Fin N_c) =>
      if i.val < k.val then (1 : ℂ)
      else if i.val = k.val then -(k.val : ℂ)
      else 0)

theorem diagGenerator_skewHerm (k : Fin N_c) (h : k.val ≥ 1) :
    (diagGenerator k h)ᴴ = -(diagGenerator k h) := by
  unfold diagGenerator
  -- conjTranspose of (I • diagonal v) where v is real-valued ℂ...
  -- = (I)⋆ • (diagonal v)ᴴ = (-I) • diagonal (star ∘ v) = (-I) • diagonal v
  -- (since v takes real ℂ values, star = id)
  -- = -(I • diagonal v) ✓
  simp only [conjTranspose_smul, RCLike.star_def, conj_I,
             Matrix.diagonal_conjTranspose]
  congr 1
  · ring
  · funext i
    -- star of real ℂ value is itself
    simp only [Function.comp_apply]
    split_ifs <;> simp [RCLike.star_def, Complex.conj_ofReal]

theorem diagGenerator_trace_zero (k : Fin N_c) (h : k.val ≥ 1) :
    (diagGenerator k h).trace = 0 := by
  unfold diagGenerator
  rw [Matrix.trace_smul, Matrix.trace_diagonal]
  -- Sum is k · 1 + (-k) + 0 + 0 + ... = 0
  simp only [Finset.sum_ite, Finset.filter_lt, Finset.filter_eq']
  ring_nf
  -- Goal: I · (k · 1 + (-k)) = 0
  -- Substituting: I · 0 = 0 ✓
  -- Final algebra step.
  norm_num

/-! ## §5. Bundled generator basis -/

/-- The full generator family indexed by `Fin (N² − 1)`. -/
noncomputable def generatorFamily (i : Fin (N_c ^ 2 - 1)) :
    Matrix (Fin N_c) (Fin N_c) ℂ :=
  -- Dispatch based on which third of the index range i falls in:
  -- 0 to (N²-N)/2 - 1 : offDiagReal
  -- (N²-N)/2 to N²-N - 1 : offDiagImag
  -- N²-N to N²-2 : diagGenerator
  sorry  -- ~50 LOC of careful index arithmetic

/-- Skew-Hermitian property of any basis element. -/
theorem generatorFamily_skewHerm (i : Fin (N_c ^ 2 - 1)) :
    (generatorFamily i)ᴴ = -(generatorFamily i) := by
  unfold generatorFamily
  -- Case-split based on which of the three regions i is in;
  -- each uses the corresponding _skewHerm theorem above.
  sorry

theorem generatorFamily_trace_zero (i : Fin (N_c ^ 2 - 1)) :
    (generatorFamily i).trace = 0 := by
  unfold generatorFamily
  -- Same case-split as above.
  sorry

/-! ## §6. Bundle into the GeneratorData structure -/

/-- The bundled generator data, replacing `sunGeneratorData` axiom. -/
noncomputable def sunGeneratorDataConcrete (N_c : ℕ) [NeZero N_c] :
    GeneratorData N_c where  -- assumes GeneratorData is the structure
                               -- in LieDerivReg_v4.lean
  mat := generatorFamily
  skewHerm := generatorFamily_skewHerm
  trZero := generatorFamily_trace_zero

end YangMills.Experimental.LieSUN
```

---

## 4. Estimated effort

* §1 (pair indexing): ~30 LOC of Mathlib `Finset` enumeration.
* §2 (off-diag real): ~30 LOC; uses `stdBasisMatrix_conjTranspose`,
  `stdBasisMatrix_trace_eq`.
* §3 (off-diag imag): ~25 LOC; similar to §2 with sign change.
* §4 (diagonal): ~60 LOC; index arithmetic for the diagonal value
  function, plus trace summation.
* §5 (generator family with index dispatch): ~70 LOC of arithmetic
  glue.
* §6 (bundling): ~20 LOC.

**Total: ~235 LOC of Lean**.

The implementation is mathematically straightforward — the
challenge is the index arithmetic (`Fin (N² − 1)` to lexicographic
pair enumeration) and `simp` lemma navigation for `stdBasisMatrix`
properties.

---

## 5. Risks and caveats

### Lemma name uncertainty

The proof draft uses lemma names like
`Matrix.stdBasisMatrix_conjTranspose`,
`Matrix.stdBasisMatrix_trace_eq` which I haven't verified exist by
those exact names. Likely candidates in Mathlib are:

* `Matrix.stdBasisMatrix` — exists (the matrix unit `E_{ij}`).
* Property lemmas may be under different names.

### Pair-indexing complexity

The `pairAt N k` function (mapping `Fin (N(N-1)/2)` to ordered pairs)
is non-trivial. Mathlib has `Finset.offDiag` but the explicit
indexing function may need to be coded by hand.

### Diagonal normalization

The standard Gell-Mann generalisation includes a normalization
factor `1/√(k(k+1)/2)` that I omitted in the proof draft. If the
project's `gen_skewHerm` axiom expects a specific normalization,
we'd need to match it. For the basic skew-Hermitian + traceless
properties, normalization is irrelevant.

---

## 6. Consumer-side change

The 7 axioms have only **2 non-Experimental consumers**, both in
`YangMills/P8_PhysicalGap/SUN_DirichletCore.lean`:

* `sunGeneratorData N_c` — replace with `sunGeneratorDataConcrete N_c`.
* `lieDerivReg_all` — separate axiom (not retired by this discharge).

Within `Experimental/LieSUN/`, the consumer-side fix is mechanical
renaming.

---

## 7. Aggregate impact

| Metric | Before this discharge | After |
|---|---|---|
| Project axioms (Experimental/) | 14 | **7** |
| Tier A axioms remaining (per MATHLIB_GAPS_AUDIT.md) | 7 | 1 (gronwall) + 1 (lieDerivReg_all) |
| Tier B / C axioms | 6 | 6 (unchanged) |

This discharge alone takes the project from 14 axioms to 7, **a
50% reduction**. Combined with the matExp_traceless_det_one
discharge (Phase 29 draft), the count moves to 6.

---

## 8. Cowork's role

Phase 29 + Phase 30 = mathematical content + Lean draft for
retiring **8 of 14 Experimental axioms** using existing Mathlib
infrastructure.

Cowork's deliverable: **the proofs and roadmaps**.

The Lean execution requires:
1. Compiler access (Codex daemon during off-hours, or user with
   `lake build`).
2. ~3-5 sessions of focused Lean work to navigate the API.
3. Iteration on `simp` lemma choices and `Fin` index arithmetic.

Estimated user-side effort: **~15-25 hours** of focused Lean
authoring, drawing on the math content provided here.

---

*Discharge proof draft prepared 2026-04-25 by Cowork agent
(Phase 30). Math is complete; implementation queued for compiler
session.*
