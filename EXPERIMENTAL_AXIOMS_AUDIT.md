# EXPERIMENTAL_AXIOMS_AUDIT.md

**Author**: Cowork agent (Claude), audit pass 2026-04-25
**Subject**: classification of the 14 axioms inside `YangMills/Experimental/`
**Question**: which can be retired (i.e. discharged into theorems), and at
what cost?

The project's strict invariant is **0 axioms outside `Experimental/`**. The
14 axioms inside that directory are the only thing standing between the
project and "0 axioms anywhere". Understanding which are retire-able and
which are genuine Mathlib-level gaps is strategic.

---

## 0. Summary

| Class | Count | Retire effort |
|---|---:|---|
| Classical, constructively provable in Lean | 7 | **easy** — ~250 LOC total in-repo |
| Classical, requires small Mathlib bridge lemma | 1 | **medium** — ~50 LOC + Mathlib PR |
| **Smuggling** (universal regularity hypothesis on arbitrary `f`) | 1 | needs **reformulation**, not retirement |
| Classical theorem, requires substantial Mathlib infrastructure | 5 | **hard** — Mathlib gaps in C₀-semigroup / weak-derivative theory |

**Action priority**: the 7 easy-retire axioms (su(N) generator data) are
straightforward Lean exercises that would reduce the project's axiom
count from 14 to 7 with no upstream dependency. The smuggling axiom
deserves immediate reformulation. The 5 hard axioms are honest gaps and
should remain `axiom` declarations until Mathlib catches up.

---

## 1. Classical, constructively provable in Lean (7 axioms)

These axioms encode the **existence and basic properties of su(N)
generators** as a basis of the Lie algebra. All of them are constructive:
the Gell-Mann matrices (N = 3), the Pauli matrices (N = 2), and the
general standard basis `{E_{ij} - E_{ji}, i(E_{ij} + E_{ji}), H_k}` are
well-defined `Matrix (Fin N) (Fin N) ℂ` objects.

### `generatorMatrix` and `generatorMatrix'`

```lean
axiom generatorMatrix (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    Matrix (Fin N_c) (Fin N_c) ℂ
```

(Same shape in `LieDerivativeRegularity.lean` and `DirichletConcrete.lean`,
with primed and unprimed names. Two separate axioms for the same concept.)

**Mathematical reading**: existence of an indexed family of `N²−1`
matrices in the Lie algebra `su(N_c)`.

**How to retire**: write down the standard basis explicitly. For each
`i : Fin (N_c ^ 2 - 1)`, decode `i` into a pair `(j, k)` and produce
either `E_{jk} - E_{kj}` (off-diagonal antisymmetric) or
`i(E_{jk} + E_{kj})` (off-diagonal symmetric, scaled) or a diagonal
generator `H_k`. Already constructive.

**Estimated effort**: ~50 LOC per file, total ~100 LOC. Should be
deduplicated by replacing both axioms with a single shared definition.

### `gen_skewHerm` and `gen_skewHerm'`

```lean
axiom gen_skewHerm (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i)ᴴ = -(generatorMatrix N_c i)
```

**Mathematical reading**: each generator is skew-hermitian.

**How to retire**: follows by direct computation from the explicit
construction in §1.1. The standard basis is built precisely to be
skew-hermitian.

**Estimated effort**: ~30 LOC per file. Trivial after the explicit
construction lands.

### `gen_trace_zero` and `gen_trace_zero'`

```lean
axiom gen_trace_zero (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1)) :
    (generatorMatrix N_c i).trace = 0
```

**Mathematical reading**: each generator is traceless.

**How to retire**: same as `gen_skewHerm` — direct computation.

**Estimated effort**: ~30 LOC per file.

### `sunGeneratorData`

```lean
axiom sunGeneratorData (N_c : ℕ) [NeZero N_c] : GeneratorData N_c
```

In `LieDerivReg_v4.lean`. Bundles the previous three axioms into a
structure.

**How to retire**: trivial after the previous three axioms are retired.
Just package the explicit constructions.

**Estimated effort**: ~10 LOC.

### Total for §1

7 axioms, ~250 LOC, **no Mathlib dependency**. Achievable as a single
focused PR. After retirement, the project has 7 axioms outside Lean's
canonical kernel — exactly the same number it has *currently inside
non-Experimental code* (= 0), bringing the total to 7.

---

## 2. Classical, requires small Mathlib bridge lemma (1 axiom)

### `matExp_traceless_det_one`

```lean
axiom matExp_traceless_det_one
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1
```

In `LieExpCurve.lean`. The file itself documents the issue:

> Blocked by: Matrix.det_exp applies to Matrix.exp ℂ, not to the
> NormedSpace.exp variant used by matExp. A bridge lemma
> `matExp_eq_matrix_exp` would close this.

**Mathematical reading**: `det(exp(t · X)) = exp(t · tr(X)) = exp(0) = 1`
when `tr X = 0`.

**Status in Mathlib**: `Matrix.det_exp` exists for `Matrix.exp` (the
matrix exponential). The project uses `matExp` which is defined via
`NormedSpace.exp` on the matrix Banach algebra. These two functions are
known to coincide on matrices over ℂ but the bridge lemma is not in
Mathlib.

**How to retire**:
1. Add `matExp_eq_matrix_exp : matExp X = Matrix.exp X` for `X : Matrix
   (Fin n) (Fin n) ℂ`. ~30 LOC. **Reasonable Mathlib upstream
   contribution** (small follow-up to the existing `Matrix.exp` API).
2. Then `matExp_traceless_det_one` follows from `Matrix.det_exp` plus
   `Real.exp_zero`.

**Estimated effort**: ~50 LOC in-repo + small Mathlib PR (or accept
in-repo as a one-line bridge if we don't want to upstream).

---

## 3. Smuggling axiom — `lieDerivReg_all` (1 axiom)

### Statement

```lean
axiom lieDerivReg_all (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : LieDerivReg' N_c f
```

In `LieDerivReg_v4.lean`. The file's own comment:

> Axiom 2: All functions on SU(N) satisfy the regularity bundle.

The bundle `LieDerivReg' N_c f` requires:
- `diff`: differentiability of `t ↦ f(lieExpCurve ... t)` at `t = 0`
- `meas`: measurability of the Lie derivative
- `sq_int`: L²-integrability of the squared Lie derivative

**Problem**: the axiom universally quantifies over **arbitrary**
`f : SUN_State_Concrete N_c → ℝ`. For a discontinuous or
non-integrable `f`, the regularity bundle does not hold. **This axiom
is mathematically false as stated.**

**Why it has not exploded**: presumably no downstream consumer applies
`lieDerivReg_all` to a discontinuous `f`. The file is in
`Experimental/` precisely as a placeholder.

**How to address**: not by retirement, but by **reformulation**. The
correct statement adds a regularity hypothesis on `f`:

```lean
theorem lieDerivReg_smooth (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (hf : ContinuouslyDiff f) :
    LieDerivReg' N_c f
```

or similar. The proof would then use the smoothness of `f` plus the
smoothness of the exponential curve.

**Estimated effort**: depends on the regularity class chosen. For a
`Continuous` hypothesis, ~100 LOC. For `ContinuouslyDiff` (smooth),
~200 LOC. The downstream call sites need to be updated to pass the
hypothesis.

**This is the most important axiom in `Experimental/` to address**,
because it is the only one that is mathematically wrong (the others
are correct but require infrastructure to prove).

---

## 4. Beurling-Deny contraction (1 axiom)

### `dirichlet_lipschitz_contraction`

```lean
axiom dirichlet_lipschitz_contraction (N_c : ℕ) [NeZero N_c]
    (φ : ℝ → ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|) (hφ0 : φ 0 = 0)
    (f : SUN_State_Concrete N_c → ℝ) :
    (∑ i, ∫ U, (lieD' N_c i (fun x => φ (f x)) U)² ∂μ) ≤
    (∑ i, ∫ U, (lieD' N_c i f U)² ∂μ)
```

**Mathematical reading**: 1-Lipschitz scalar maps `φ` do not increase
Dirichlet energy. This is the **Beurling-Deny contraction property**
(Bourbaki / Fukushima).

**Status in Mathlib**: the abstract Beurling-Deny criteria for Dirichlet
forms are not yet formalised. Proving this on a Lie group additionally
requires weak derivatives, which Mathlib's Dirichlet form
infrastructure does not currently support beyond the Markov-chain case.

**How to retire**: requires Mathlib upstream work on:
- Weak derivatives on Lie groups (or at least on compact Riemannian
  manifolds).
- Dirichlet form abstract API with the Beurling-Deny axioms.

**Estimated effort**: substantial. ~1000+ LOC of Mathlib work, or a
project-local construction tied to the specific SU(N) Dirichlet form
which is partially built in the project.

**Recommendation**: keep as `axiom` for now. Document carefully with a
"requires Mathlib weak-derivative infrastructure" tag.

---

## 5. Hille-Yosida + Poincaré → variance decay (4 axioms)

### `hille_yosida_core`

```lean
axiom hille_yosida_core
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) :
    SymmetricMarkovTransport μ
```

**Mathematical reading**: the Hille-Yosida theorem applied to a
strong Dirichlet form yields a symmetric Markov semigroup.

### `poincare_to_variance_decay`

```lean
axiom poincare_to_variance_decay
    ... (hP : PoincareInequality μ E lam) :
    HasVarianceDecay sg
```

**Mathematical reading**: Poincaré inequality + symmetric semigroup ⇒
exponential variance decay (Gronwall-type argument).

### `variance_decay_from_bridge_and_poincare_semigroup_gap` and
### `gronwall_variance_decay`

Variants of the above with different bridge structures.

**Status in Mathlib**: C₀-semigroup theory is partially in Mathlib
(`Mathlib.Analysis.NormedSpace.Hahn`, `Mathlib.Analysis.NormedSpace.OperatorNorm`),
but the Hille-Yosida theorem in the form needed (Markov / Dirichlet
case) is not. The Gronwall ODE machinery exists but is not coupled to
the variance-decay framework.

**How to retire**: requires significant Mathlib infrastructure work
on:
- Strongly continuous semigroups of operators.
- Hille-Yosida theorem for Markov generators.
- Variance/entropy decay via spectral / ODE arguments.

**Estimated effort**: substantial. Each is at the level of ~500 LOC
Mathlib infrastructure, and the Hille-Yosida + Markov coupling is a
recognised hard formalisation target.

**Recommendation**: keep as `axiom` for now. These are honest
"upstream needed" gaps, not in scope for the project's near-term
horizon.

---

## 6. Action plan

### Immediate (this month)

- [ ] **Retire the 7 generator-data axioms** (~250 LOC, no Mathlib
      dependency). High value: drops axiom count by half. Good Codex
      target after the F3-Count witness lands.
- [ ] **Reformulate `lieDerivReg_all`** with a regularity hypothesis.
      Update all callers. Even if the new hypothesis is not yet
      provable for every f, the smuggling is fixed.
- [ ] **Retire `matExp_traceless_det_one`** via the bridge lemma.
      Optional: open the bridge lemma as a Mathlib PR for upstream
      benefit.

### Long-term (months / years)

- [ ] Track Mathlib progress on Hille-Yosida, Beurling-Deny, weak
      derivatives. Retire each axiom as the upstream infrastructure
      lands.

### Documentation

- [ ] Update `AXIOM_FRONTIER.md` with this audit's classification —
      currently the file lists all 14 axioms but doesn't distinguish
      easy-retire from hard-retire.
- [ ] Update `STATE_OF_THE_PROJECT.md` "What is open" table to mention
      that the 14 Experimental axioms are not on the Clay critical
      path but 7 of them are easy in-repo wins.

---

## 7. Side observation: duplication

Three axioms appear with primed and unprimed names:

- `generatorMatrix` (LieDerivativeRegularity) ≈ `generatorMatrix'`
  (DirichletConcrete) ≈ `sunGeneratorData.mat` (LieDerivReg_v4).
- `gen_skewHerm` ≈ `gen_skewHerm'` ≈ `sunGeneratorData.skewHerm`.
- `gen_trace_zero` ≈ `gen_trace_zero'` ≈ `sunGeneratorData.trZero`.

These are three parallel attempts at the same data, presumably from
different sessions of project development. **Deduplication** would
itself drop the axiom count by 4 (from 7 to 3 in this category)
without any new mathematical content — purely refactoring. Worth
doing during the §6 retirement work.

---

*Audit complete 2026-04-25 by Cowork agent.*

---

## ∞. Late-session update (2026-04-25 evening)

This audit was written when the project had **14 axioms** in
`Experimental/`. After Phases 33 + 35 (2026-04-25 morning, before
the late session), the count was reduced to **7 axioms** via:

* **Phase 33**: deletion of 3 truly orphan axioms
  (`dirichlet_lipschitz_contraction`, `hille_yosida_core`,
  `poincare_to_variance_decay`).
* **Phase 35**: deduplication of 4 axioms (`generatorMatrix'`,
  `gen_skewHerm'`, `gen_trace_zero'`, `sunGeneratorData`) by
  importing `LieDerivativeRegularity.lean` and replacing primed
  axioms with `def` aliases.

After the late-session work (Phases 49–79):

| Axiom | Status post-late-session |
|-------|-------------------------|
| `generatorMatrix` | unchanged (data axiom; vacuously usable at `N_c = 1`) |
| `gen_skewHerm` | unchanged + **theorem-form discharge at `N_c = 1`** via `Fin.elim0` (Phase 64) |
| `gen_trace_zero` | unchanged + **theorem-form discharge at `N_c = 1`** via `Fin.elim0` (Phase 64) |
| `lieDerivReg_all` | unchanged (substantive smuggling; needs reformulation) |
| `matExp_traceless_det_one` | unchanged + **two theorem-form discharges at `n = 1`** via `MatExpTracelessDimOne.lean` (Phase 62, direct) and `MatExpDetTraceDimOne.lean` (Phase 77, via more general `det(exp) = exp(trace)` at n=1); Mathlib upstream TODO confirmed at `Analysis/Normed/Algebra/MatrixExponential.lean` line 57 |
| `gronwall_variance_decay` | unchanged (Mathlib upstream gap; C₀-semigroup theory) |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | unchanged (same root) |

**Net result of late-session work on the axiom frontier**:

* The **7-axiom count is unchanged**.
* **3 of 7 axioms now have theorem-form discharges at the
  `N_c = 1` / `n = 1` base case**, serving as Mathlib-PR fixtures
  for any future general retirement.
* The remaining 4 axioms are genuine Mathlib upstream gaps
  (`lieDerivReg_all` needs reformulation;
  `gronwall_variance_decay` and
  `variance_decay_from_bridge_and_poincare_semigroup_gap` need
  C₀-semigroup theory; `generatorMatrix` is a data axiom whose
  retirement would require constructing an explicit SU(N)
  generator basis).

Cross-references:
- `MATEXP_DET_ONE_DISCHARGE_PROOF.md` §7 (Phase 78 update).
- `YangMills/Experimental/LieSUN/MatExpDetTraceDimOne.lean` (Phase 77).
- `YangMills/Experimental/LieSUN/GeneratorAxiomsDimOne.lean` (Phase 64).
- `YangMills/Experimental/LieSUN/MatExpTracelessDimOne.lean` (Phase 62).
- `COWORK_FINDINGS.md` Findings 010, 014.

---

## 8. Phase 27 update — Consumer matrix

**Date**: 2026-04-25 (later in session, Phase 27)

Re-audit with explicit consumer counting (`grep -rln <axiom> YangMills
--include='*.lean' | grep -v Experimental | wc -l`):

| Axiom | Non-Experimental consumers |
|---|---:|
| `generatorMatrix` | **0** |
| `gen_skewHerm` | **0** |
| `gen_trace_zero` | **0** |
| `generatorMatrix'` | **0** |
| `gen_skewHerm'` | **0** |
| `gen_trace_zero'` | **0** |
| `dirichlet_lipschitz_contraction` | **0** |
| `sunGeneratorData` | 1 |
| `lieDerivReg_all` | 1 |
| `matExp_traceless_det_one` | **0** |
| `hille_yosida_core` | **0** |
| `poincare_to_variance_decay` | **0** |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | **0** |
| `gronwall_variance_decay` | **0** |

**Critical findings**:

1. **12 of 14 axioms have ZERO non-Experimental consumers**. They
   are entirely contained within the `Experimental/` directory and
   contribute NOTHING to any downstream proof obligation.

2. **The 2 axioms with 1 consumer each** (`sunGeneratorData`,
   `lieDerivReg_all`) are both consumed by
   `YangMills/P8_PhysicalGap/SUN_DirichletCore.lean` — the Phase 8
   Physical-side stack, NOT the Clay chain.

3. **Zero axioms are consumed by the Clay chain**
   (`ClayCore/ClayUnconditional.lean` and downstream). The Clay
   deliverable is fully independent of the Experimental directory.

### Strategic implication

For Practical Clay closure (`ClayYangMillsPhysicalStrong_Genuine`),
the Experimental axioms are **non-load-bearing**. The project can
honestly claim:

> "The Clay chain (`clay_yangMills_theorem_from_balaban` and the
> `SUNWilsonBridgeData → ClayYangMillsTheorem` projection) is
> sorry-free, oracle-clean, and uses only the standard kernel axioms
> `[propext, Classical.choice, Quot.sound]`. The 14 axioms in
> `Experimental/` are placeholders for a parallel Phase 8 effort
> (Dirichlet form / LSI / Poincaré route to mass gap) and are NOT
> consumed by the cluster-expansion / Bałaban Clay route."

This is a **stronger claim** than the audit originally identified:
the project's Clay chain is more independent of Experimental than
the categorization in §1-§7 suggested.

### Cowork's recommendation

For the project's Clay deliverable, **leave Experimental alone**.
The 14 axioms are placeholder content for a separate (and
currently lower-priority) line of work. Any retirement effort there
should be driven by the consumers (`P8_PhysicalGap/SUN_DirichletCore.lean`)
maturing first.

For documentation / external communication: the project should
clearly label `Experimental/` as "non-load-bearing for Clay" and
focus the unconditionality narrative on `ClayCore/`.

---

*Phase 27 update added 2026-04-25 by Cowork agent. The consumer
matrix shifts the strategic posture: Experimental axioms are
research-level placeholders that don't compromise the Clay chain.*
