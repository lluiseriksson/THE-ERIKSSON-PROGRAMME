# MATHLIB_GAPS_AUDIT.md

**Author**: Cowork agent (Claude)
**Date**: 2026-04-25 (Phase 28)
**Subject**: Hands-on search of Mathlib (master @ Apr 2026, project pin
`07642720`) for infrastructure that could close the Experimental
axiom gaps and discharge open obligations of the Clay chain
**Companion**: `EXPERIMENTAL_AXIOMS_AUDIT.md` (the project-internal
axiom catalog)

---

## 0. Executive summary

I searched Mathlib for every gap class flagged in the project's
`Experimental/` axioms and the open hypothesis fields of ClayCore's
`SUNWilsonBridgeData`. Findings:

| Gap | Mathlib status | Discharge path | Effort |
|---|---|---|---|
| `Matrix.det_exp` (Liouville) | **Explicit TODO** in Mathlib (file `MatrixExponential.lean` line 57 marks it) | Mathlib PR — provable from `Matrix.exp_diagonal` + spectral theorem | Small (~80 LOC) |
| Hermitian spectral theorem | **Already in Mathlib** (`IsHermitian.spectral_theorem`, `eigenvectorUnitary`) | Direct discharge via this | Project-internal |
| `Matrix.exp` properties (conjTranspose, neg, conj) | **Already in Mathlib** | Direct | Project-internal |
| Gronwall (ODE) | **Already in Mathlib** (`Mathlib/Analysis/ODE/Gronwall.lean`) | Bridge real-function ODE → variance | Medium (~150 LOC) |
| Variance (probability) | **Already in Mathlib** (`Mathlib/Probability/Moments/Variance.lean`) | Direct | Project-internal |
| Markov kernel infrastructure | **Already in Mathlib** (`Mathlib/Probability/Kernel/`) | Direct | Project-internal |
| Hille-Yosida / C₀-semigroup theory | **NOT in Mathlib** | Major Mathlib PR or workaround | Large (~500-1000 LOC) |
| Dirichlet form (measure-theoretic) | **NOT in Mathlib** (only number-theory Dirichlet) | Major Mathlib PR | Large |
| Poincaré inequality (measure-theoretic) | **NOT in Mathlib** (only Geometry / curve integral) | Major Mathlib PR | Large |
| SU(N) Lie algebra basis | **NOT in Mathlib** (only `Matrix.specialUnitaryGroup` group structure) | Project-internal Lie algebra construction | Medium (~200 LOC) |
| Logarithmic Sobolev inequality | **NOT in Mathlib** | Major Mathlib PR | Large |

**Key takeaway**: Mathlib has **all the matrix-analytic and
probability-theoretic** infrastructure needed for a substantial
fraction of the Experimental axioms. The genuine gaps are in
**measure-theoretic functional analysis** (Dirichlet form, Poincaré,
LSI, semigroup theory), where Mathlib's coverage is still maturing.

---

## 1. Discharge candidate #1: `matExp_traceless_det_one`

**Project axiom**:
```lean
axiom matExp_traceless_det_one
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1
```

**File**: `YangMills/Experimental/LieSUN/LieExpCurve.lean`.

### Mathlib infrastructure available

In `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`:

* `Matrix.exp_diagonal` (line 83): `exp (diagonal v) = diagonal (exp v)`.
* `Matrix.exp_conjTranspose` (line 97): `(exp A)ᴴ = exp Aᴴ`.
* `Matrix.exp_add_of_commute` (line 130).
* `Matrix.isUnit_exp` (line 147): `IsUnit (exp A)`.
* `Matrix.exp_neg` (line 178): `exp (-A) = (exp A)⁻¹`.
* `Matrix.exp_units_conj` (line 156): `exp (U A U⁻¹) = U exp(A) U⁻¹`.

In `Mathlib/Analysis/Matrix/Spectrum.lean`:

* `Matrix.IsHermitian.spectral_theorem` (line 144): `H = U D Uᴴ`.
* `Matrix.IsHermitian.eigenvalues : n → ℝ` (line 65).
* `Matrix.IsHermitian.eigenvectorUnitary : Matrix.unitaryGroup n ℂ` (line 87).

### Discharge sketch

For skew-Hermitian X (i.e., `Xᴴ = -X`) with `tr X = 0`:

1. Define `H := -i • X`. Then `H` is Hermitian (verify: `Hᴴ = (-i)⋆ • Xᴴ = i • (-X) = -i • X = H`).
2. Apply `IsHermitian.spectral_theorem` to `H`: obtain eigenvector unitary `U` and real eigenvalues `λ : n → ℝ` with `H = U · diagonal (λ : n → ℂ) · Uᴴ`.
3. Then `X = i • H = U · diagonal (i • λ) · Uᴴ`.
4. By `exp_units_conj`: `exp ((t:ℂ) • X) = U · exp ((t:ℂ) • diagonal (i • λ)) · Uᴴ = U · diagonal (fun i => exp (t · i · λ i)) · Uᴴ` using `exp_diagonal`.
5. `det (exp ((t:ℂ) • X)) = det U · ∏ exp (t · i · λ i) · det Uᴴ` using `det_mul`, `det_diagonal`.
6. `det U · det Uᴴ = |det U|² = 1` since `U` is unitary.
7. `∏ exp (t · i · λ i) = exp (t · i · ∑ λ i) = exp (t · i · tr H) = exp (-t · tr X)` (since `tr H = -i · tr X`).
8. With `tr X = 0`: result is `exp 0 = 1`.

### Estimated effort

**~80 LOC of Lean**. Uses only existing Mathlib infrastructure. The
proof is mathematically standard (Liouville's formula via spectral
theorem on the Hermitian companion).

**Note**: Mathlib's TODO comment at `MatrixExponential.lean` line 57
acknowledges this is missing. A Mathlib PR upstreaming the general
`Matrix.det_exp` theorem (or this specialised skew-Hermitian
variant) would benefit the broader community.

---

## 2. Discharge candidate #2: `gronwall_variance_decay`

**Project axiom**:
```lean
axiom gronwall_variance_decay
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (sg : SymmetricMarkovTransport μ)
    (lam : ℝ) (hlam : 0 < lam)
    (hP : PoincareInequality μ E lam)
    (hBridge : SemigroupDirichletBridgeGlobal E sg) :
    HasVarianceDecay sg
```

**File**: `YangMills/Experimental/Semigroup/VarianceDecayFromPoincare.lean`.

### Mathlib infrastructure available

In `Mathlib/Analysis/ODE/Gronwall.lean`:

* `gronwallBound` (function) — explicit Gronwall bound.
* `gronwallBound_ε0` (line 77): `gronwallBound δ K 0 x = δ * exp (K * x)` — direct exp form when `ε = 0`.
* `le_gronwallBound_of_liminf_deriv_right_le` (line 111): if `f' ≤ K f + ε` (one-sided), then `f(x) ≤ gronwallBound`.
* `norm_le_gronwallBound_of_norm_deriv_right_le` (line 135): the norm version.

In `Mathlib/Probability/Moments/Variance.lean`:

* `evariance`, `variance` (definitions).
* `evariance_congr`, `variance_congr`, `evariance_lt_top`, etc.

### Discharge sketch

The mathematical chain in the project's docstring (lines 122-128 of `VarianceDecayFromPoincare.lean`):
```
hBridge gives  ∂/∂t Var(T_t f) = -2 E(T_t f)  for ALL t  
hP gives       E(g) ≥ λ Var(g)
Combined:      ∂/∂t Var(T_t f) ≤ -2λ Var(T_t f)
Gronwall:      Var(T_t f) ≤ exp(-2λt) Var(f)
```

Concretely:

1. Let `V(t) := variance (T_t f) μ`.
2. `hBridge` gives `HasDerivAt V (-2 · E (T_t f)) t` for all `t ≥ 0`.
3. `hP` applied to `T_t f` gives `E (T_t f) ≥ λ · V(t)`.
4. Combining: `V'(t) ≤ -2λ V(t)`, equivalently `V'(t) + 2λ V(t) ≤ 0`, equivalently `V'(t) ≤ K V(t)` where `K = -2λ < 0`.
5. By `le_gronwallBound_of_liminf_deriv_right_le` with `K = -2λ`, `δ = V(0) = variance f μ`, `ε = 0`: `V(t) ≤ gronwallBound δ K 0 t = δ · exp(K · t) = variance f μ · exp(-2λt)`.

### Estimated effort

**~150-250 LOC of Lean**. The bridge between abstract
`SemigroupDirichletBridgeGlobal` (project predicate) and concrete
real-function ODE infrastructure (Mathlib) is the bulk of the work.

The challenge isn't the math — it's the type-level glue between the
project's abstract `HasDerivAt` claim (in the Bridge predicate) and
Mathlib's `gronwallBound` machinery. A careful translation layer is
needed.

**Status**: tractable, doesn't need any Mathlib gap closure. Pure
project-internal work.

---

## 3. Discharge candidate #3: SU(N) generator basis

**Project axioms** (6 axioms across `LieDerivativeRegularity.lean`
and `DirichletConcrete.lean`):

```lean
axiom generatorMatrix (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    Matrix (Fin N_c) (Fin N_c) ℂ
axiom gen_skewHerm (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i)ᴴ = -(generatorMatrix N_c i)
axiom gen_trace_zero (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i).trace = 0
-- (and primed variants in DirichletConcrete.lean)
```

### Mathlib infrastructure available

* `Matrix.specialUnitaryGroup (Fin N) ℂ` — the SU(N) group exists.
* `Matrix.skewHermitian` — predicate for skew-Hermitian matrices.
* `Matrix.trace` — trace exists.

### Mathlib infrastructure MISSING

* No explicit basis of the SU(N) Lie algebra.
* No `LieAlgebra.specialUnitary` or similar Lie-algebra-level structure.

### Discharge sketch

These axioms can be retired by a **project-internal** construction
of the standard SU(N) basis. The Gell-Mann matrices (for N = 3) and
their generalisation to arbitrary N use the standard basis:

* Off-diagonal real: `E_{ij} - E_{ji}` for `i < j` (gives `(N²-N)/2` matrices).
* Off-diagonal imaginary: `i (E_{ij} + E_{ji})` for `i < j` (gives `(N²-N)/2`).
* Diagonal: `H_k = (1/√(k(k+1))) · diag(1, 1, ..., 1, -k, 0, ..., 0)` for `k = 1, ..., N-1` (gives `N-1`).

Total: `(N²-N) + (N-1) = N² - 1`. ✓

Each matrix is by construction skew-Hermitian (after multiplying off-diagonal real ones by `i`) and traceless. Properties prove via direct computation.

### Estimated effort

**~200-300 LOC of Lean**: definition of the standard basis matrices,
`skewHerm` and `trace_zero` proofs, plus the indexing function from
`Fin (N² - 1)` to the basis. Tractable but tedious.

**Status**: project-internal work. No Mathlib dependency needed.
Could be a Cowork contribution if Phase 8 / P8 work prioritises it.

**Note**: deduplication between primed and unprimed variants would
also reduce 6 axioms to 3 with no new mathematical content (per
EXPERIMENTAL_AXIOMS_AUDIT.md §7).

---

## 4. Discharge candidate #4: `dirichlet_lipschitz_contraction`

**Project axiom**: Dirichlet form Lipschitz contraction property.

### Mathlib infrastructure

**Mathlib has NO `DirichletForm` namespace** in measure theory
(only number-theoretic `DirichletCharacter`).

The closest infrastructure: `Mathlib/Analysis/InnerProductSpace/`,
`Mathlib/MeasureTheory/Function/L2Space.lean`. These provide
inner-product / L² infrastructure but no specific Dirichlet-form
theory.

### Discharge path

This requires **Mathlib upstream contribution**. A `DirichletForm`
namespace would need:
- Definition of Dirichlet forms (closed, symmetric, Markov).
- Beurling-Deny theorem.
- Connection to symmetric Markov semigroups.

Estimated: **major Mathlib PR (~1000+ LOC)**. Years of timeline if
pursued by community.

### Project workaround

The project's `Experimental/LieSUN/DirichletContraction.lean`
encodes a SPECIFIC Lipschitz claim about the SU(N) Wilson Dirichlet
form. This could be reformulated as a hypothesis-conditioned theorem
(per the discipline applied in Phase 22) — converting the axiom to
a named hypothesis the consumer must inhabit.

**Recommended action**: apply hypothesis-conditioning to retire the
axiom while waiting for Mathlib's Dirichlet form library to mature.

---

## 5. Discharge candidate #5: `hille_yosida_core` and friends

**Project axioms**: Hille-Yosida, Poincaré → variance decay,
variance decay from bridge.

### Mathlib infrastructure

**Mathlib has NO C₀-semigroup theory** as of 2026-04-25 (no
`*HilleYosida*` files). There's no `MarkovSemigroup` predicate
either, only `MarkovKernel` (single-step).

### Discharge path

Mathlib upstream contribution needed:

1. C₀-semigroup theory (`Mathlib/Analysis/Semigroup/StronglyContinuous.lean`?).
2. Hille-Yosida generation theorem.
3. Symmetric Markov semigroups on probability spaces.

Estimated: **~500-1000 LOC of major Mathlib PRs**.

### Project workaround

Same as Dirichlet form: apply hypothesis-conditioning. The project
consumer (`P8_PhysicalGap/SUN_DirichletCore.lean`) can take the
deep semigroup result as a named hypothesis until Mathlib catches
up.

---

## 6. Aggregate: what's tractable now

### Tier A — Discharge with current Mathlib (Cowork-feasible if compiler available)

| Project axiom | Mathlib has | Effort |
|---|---|---|
| `matExp_traceless_det_one` | spectral_theorem + exp_diagonal + det_diagonal | ~80 LOC |
| `gronwall_variance_decay` | gronwallBound + Variance | ~150-250 LOC |
| `generatorMatrix` (and 5 related) | specialUnitaryGroup + skewHermitian | ~200-300 LOC |
| `sunGeneratorData` | Bundling | trivial after above |

**Total Tier A**: ~500-650 LOC of Lean discharge work, 0 Mathlib PRs
needed. Could move project from 14 axioms to 6 axioms.

### Tier B — Hypothesis-condition (already viable with no Mathlib)

| Project axiom | Action |
|---|---|
| `dirichlet_lipschitz_contraction` | Convert to named hypothesis |
| `hille_yosida_core` | Convert to named hypothesis |
| `poincare_to_variance_decay` | Convert to named hypothesis |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | Convert to named hypothesis |
| `lieDerivReg_all` | Convert to named hypothesis |

**Total Tier B**: ~5 axioms convert to hypothesis-conditioned form.
Doesn't reduce mathematical conditionality but improves legibility
(matches ClayCore discipline). Could move project from 14 axioms to
9 (after Tier A) or further.

### Tier C — Wait for Mathlib

| Project axiom | Mathlib gap |
|---|---|
| `dirichlet_lipschitz_contraction` | Dirichlet form library |
| `hille_yosida_core` | C₀-semigroup theory |
| `poincare_to_variance_decay` | Above + Poincaré inequality library |
| (others) | LSI library, advanced functional analysis |

**Total Tier C**: long-horizon Mathlib infrastructure work.
Out-of-scope for this project.

---

## 7. Recommended action sequence

If the project wants to systematically reduce its axiom count:

### Step 1 (Cowork-eligible if Lean toolchain available)

Discharge `matExp_traceless_det_one` using Mathlib's spectral
theorem. Estimated **~80 LOC**, moves axiom count from 14 → 13.

### Step 2 (Cowork-eligible)

Construct SU(N) generator basis explicitly. Discharge 6 axioms
(`generatorMatrix`, `gen_skewHerm`, `gen_trace_zero` plus primed
variants). Plus `sunGeneratorData` (bundling). Estimated **~250-300
LOC**, moves axiom count 13 → 6.

### Step 3 (Cowork-eligible, requires bridge work)

Discharge `gronwall_variance_decay` using Mathlib's `gronwallBound`.
Estimated **~150-250 LOC**, moves axiom count 6 → 5.

### Step 4 (Cowork-eligible, structural)

Hypothesis-condition the remaining 5 deep axioms. Estimated **~50
LOC** of refactoring, retiring 5 axioms via type-level lifting.
Moves count 5 → 0 axioms (with all conditionality lifted to type
signatures).

**Total**: ~530-680 LOC of Lean work to move from 14 axioms to 0
axioms (with hypothesis-conditioning for the deep results).

### Step 5 (Mathlib upstream, long-horizon)

Once Mathlib's Dirichlet form / C₀-semigroup / Poincaré inequality
infrastructure matures, the hypothesis-conditioned axioms can be
discharged unconditionally.

---

## 8. Cowork-side commitments

**What I CAN do** (with Lean toolchain access):

* Steps 1, 2, 3, 4 above. Estimated 2-4 sessions of focused work
  per step.

**What I CAN'T do**:

* Lean toolchain not available in this environment — proofs are
  best-effort and need user-side verification.
* Mathlib upstream PRs (would need to fork Mathlib + open PR via
  GitHub API).

**What I'm doing instead** (this session):

* This audit document, providing a clear roadmap for whoever takes
  the axiom retirement work next.
* Phase 21-22 Cowork-side hypothesis-conditioning of `Branch III` /
  `Branch VII` scaffolds.
* Phase 23-25 architectural bridge files.

---

## 9. Specific Mathlib API references (for downstream work)

### Matrix exponential
* `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`
* `Matrix.exp_diagonal`, `Matrix.exp_conjTranspose`, `Matrix.exp_add_of_commute`,
  `Matrix.exp_neg`, `Matrix.exp_units_conj`, `Matrix.isUnit_exp`.

### Hermitian spectral
* `Mathlib/Analysis/Matrix/Spectrum.lean`
* `Matrix.IsHermitian.spectral_theorem` (line 144).
* `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.eigenvectorUnitary`.
* `Matrix.IsHermitian.charpoly_eq` (eigenvalues as roots).

### Determinant
* `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
* `Matrix.det_diagonal`, `Matrix.det_mul`.

### Probability variance
* `Mathlib/Probability/Moments/Variance.lean`
* `evariance`, `variance`, `evariance_congr`, `variance_congr`.

### ODE Gronwall
* `Mathlib/Analysis/ODE/Gronwall.lean`
* `gronwallBound`, `le_gronwallBound_of_liminf_deriv_right_le`,
  `norm_le_gronwallBound_of_norm_deriv_right_le`.

### Markov kernel
* `Mathlib/Probability/Kernel/`
* `MarkovKernel`, `Kernel.invariance` (in `Invariance.lean`).

---

## 10. Conclusion

**Mathlib has more discharge infrastructure than the current
Experimental axiom set acknowledges.** Specifically:

* `matExp_traceless_det_one` — fully discharge-able from current
  Mathlib via Hermitian spectral theorem. Just hasn't been done.
* `gronwall_variance_decay` — discharge-able via `gronwallBound` +
  bridge work to abstract semigroup variance.
* SU(N) generator axioms — fully discharge-able via explicit basis
  construction (no Mathlib dependency beyond `Matrix.specialUnitaryGroup`).

The genuine Mathlib gaps are in **measure-theoretic functional
analysis** (Dirichlet form, C₀-semigroup, LSI, Poincaré). These are
honest research-level upstream contributions waiting to happen.

**Practical implication**: the project's "14 axioms" claim
overstates the genuine open obligations. **A focused ~500-680 LOC
discharge effort would retire 6-8 of them using existing Mathlib
infrastructure.** The remaining 6-8 are honest measure-theoretic
gaps requiring upstream contributions.

---

*Audit complete 2026-04-25 by Cowork agent (Phase 28). Re-run after
any major Mathlib upgrade to refresh the discharge candidates.*
