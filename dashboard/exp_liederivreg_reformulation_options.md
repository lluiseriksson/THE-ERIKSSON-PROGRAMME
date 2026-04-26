# exp_liederivreg_reformulation_options.md

**Cowork-authored reformulation-strategy scope for `EXP-LIEDERIVREG`.**
**Filed: 2026-04-26T19:20:00Z by Cowork.**
**Loop-input for the eventual replacement of `axiom lieDerivReg_all` per
`UNCONDITIONALITY_LEDGER.md:109` ("Restrict to smooth f"); Cowork audit ⇒ Codex
implementation; no Lean edit performed by Cowork.**

This file is a Cowork **scoping** document. Cowork has not proved any reformulation
and is not patching the existing INVALID axiom. The axiom must be **REPLACED**.
This document enumerates concrete replacement strategies + downstream consumer
impact + a recommended option for Codex to implement.

---

## (a) Existing axiom + consumer inventory

### The axiom (`LieDerivReg_v4.lean:58`)

```lean
/-- Axiom 2: All functions on SU(N) satisfy the regularity bundle. -/
axiom lieDerivReg_all (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : LieDerivReg' N_c f
```

The regularity bundle `LieDerivReg' N_c f` (`LieDerivReg_v4.lean:50–55`) has
three fields:

| Field | Statement (informal) |
|---|---|
| `diff` | For every generator index `i` and every `U : SUN_State_Concrete N_c`, the function `t ↦ f(lieExpCurve i U t)` is differentiable at `0` |
| `meas` | For every `i`, the Lie derivative `lieD' N_c i f` is `AEStronglyMeasurable` w.r.t. `sunHaarProb N_c` |
| `sq_int` | For every `i`, the squared Lie derivative `(lieD' N_c i f U)^2` is `Integrable` w.r.t. `sunHaarProb N_c` |

### Why the axiom is INVALID as stated

The axiom claims **every** function `f : SUN_State_Concrete N_c → ℝ` satisfies
all three fields. This is mathematically false:

1. **Counter-example for `diff`**: take `f` to be the indicator function of a
   positive-but-not-full-measure subset. `t ↦ f(lieExpCurve i U t)` jumps
   discontinuously and is not differentiable at most `t = 0`.
2. **Counter-example for `meas` + `sq_int`**: take `f` non-measurable (such
   functions exist by AC). The Lie derivative is not defined a.e., let alone
   measurable or square-integrable.

The axiom must be replaced by a typed hypothesis or by a smaller universe of `f`.

### Consumer inventory (3 files, confirmed by `Grep "lieDerivReg_all"` at 19:10Z freshness audit)

| File | Lines | Consumer | Math content |
|---|---:|---|---|
| `Experimental/LieSUN/LieDerivReg_v4.lean` | 70-77 | `lieD'_add` (theorem) | `lieD' i (f+g) U = lieD' i f U + lieD' i g U`; uses `lieDerivReg_all N_c f .diff` and `lieDerivReg_all N_c g .diff` |
| `Experimental/LieSUN/LieDerivReg_v4.lean` | 80-87 | `lieD'_smul` (theorem) | `lieD' i (c · f) U = c · lieD' i f U`; uses `lieDerivReg_all N_c f .diff` |
| `Experimental/LieSUN/LieDerivReg_v4.lean` | 94-125 | `dirichletForm''_subadditive` (theorem) | `E(f+g) ≤ 2·E(f) + 2·E(g)` (subadditivity); uses `.sq_int` for all three of `f`, `g`, `f+g` |
| `Experimental/LieSUN/GeneratorAxiomsDimOne.lean` | 56 | comment-only mention in a "requires deeper work" table | not an active consumer |
| `P8_PhysicalGap/SUN_DirichletCore.lean` | 108-145 | `sunDirichletForm_subadditive` (theorem, **outside** Experimental/) | `E(f+g) ≤ 2·E(f) + 2·E(g)` for the canonical `lieDerivative`; uses `lieDerivReg_all` for `f`, `g`, `f+g` |

The active consumers all need:
- `.diff f` to algebraically manipulate `lieD' i (f+g) = lieD' i f + lieD' i g`
- `.sq_int f` to invoke `integral_mono` / `Integrable.const_mul` / `Integrable.add`

The `meas` field is currently unused by the active consumers (it provides
infrastructure that follows from `sq_int` for the project's purposes).

---

## (b) Concrete reformulation options

Three viable options. Cowork lists them in increasing order of refactor cost.

### Option 1 — Eliminate the axiom; pass `LieDerivReg' f` as an explicit hypothesis

**Strategy**: delete the `axiom lieDerivReg_all` line. Every consumer theorem
takes `(hf : LieDerivReg' N_c f)` (and `hg`, `hfg` where needed) as an explicit
hypothesis.

**Proposed Lean signature changes**:

```lean
-- (was) theorem lieD'_add {…} : … := … (lieDerivReg_all N_c f).diff …
-- (after) :
theorem lieD'_add {…} (hf : LieDerivReg' N_c f) (hg : LieDerivReg' N_c g)
    (i : Fin (N_c^2 - 1)) (U : SUN_State_Concrete N_c) :
    lieD' N_c i (fun x => f x + g x) U = lieD' N_c i f U + lieD' N_c i g U := by
  simp only [lieD']; set gd := sunGeneratorData N_c
  exact lieDerivExp_add (gd.mat i) (gd.skewHerm i) (gd.trZero i) f g U
    (hf.diff i U) (hg.diff i U)

-- (analogously) lieD'_smul, dirichletForm''_subadditive,
-- sunDirichletForm_subadditive
```

**Pros**:
- Eliminates the axiom **entirely**. The `LieDerivReg'` structure already exists
  (`LieDerivReg_v4.lean:50`); no new types needed.
- Math is provably correct as stated: "for every `f` admitting Lie regularity,
  `lieD'_add` holds, etc."
- Mathlib pre-check: zero new helpers needed; existing `LieDerivReg'`
  structure is the natural typeclass-style hypothesis.
- The `meas` + `sq_int` fields are honest carriers of the missing analytic
  content — until a downstream consumer **proves** `LieDerivReg' f` for a
  concrete class of `f`, the subadditivity statement is conditional on the
  hypothesis (which is now what the math actually says).

**Cons**:
- Refactor cost: 4 consumer theorem signatures change (3 in Experimental/,
  1 in P8_PhysicalGap/).
- Downstream call-sites of `dirichletForm''_subadditive` and
  `sunDirichletForm_subadditive` must now also supply `LieDerivReg'` evidence
  (which has to come from somewhere — either a future smooth-functions theorem
  or an additional hypothesis at the next level up). This is **honest**: the
  conditional structure is propagated.

**Tier 2 axiom impact**: -1 (axiom retired). Tier 2 count goes 5 → 4.

### Option 2 — Restrict to smooth functions

**Strategy**: replace `lieDerivReg_all` by a theorem proven for `f` satisfying
`ContDiff ℝ ⊤ f`. SU(N) is a compact Lie group (or at least `SUN_State_Concrete N_c`
is the underlying compact manifold), so for smooth `f`:

- `diff` follows from `ContDiff` + `lieExpCurve` smooth in `t`.
- `meas` follows: smooth implies continuous implies measurable.
- `sq_int` follows: continuous on compact ⇒ bounded ⇒ Lp.

**Proposed Lean signature**:

```lean
theorem lieDerivReg_smooth (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (hf : ContDiff ℝ ⊤ f) :
    LieDerivReg' N_c f
```

**Pros**:
- Mathematically standard.
- One theorem closes the gap for every smooth `f`.
- Mathlib helpers: `ContDiff.differentiable`, `ContDiff.continuous`,
  `Continuous.aestronglyMeasurable`, `IsCompact.continuous_integrable_pow`,
  `MeasureTheory.IsCompact.bounded_continuous_function_le_iff`,
  `MeasureTheory.Memℒp` / `Lp` machinery.
- For most practical Wilson-functional applications (correlator
  observables, polynomial-in-trace functions), `f` is smooth ⇒ this option
  covers all real use cases.

**Cons**:
- Refactor cost: same as Option 1 plus the smoothness theorem (~80 LOC for
  the proof itself, ~100 LOC of consumer signature changes).
- Downstream: every consumer must now have `(hf : ContDiff ℝ ⊤ f)`
  hypothesis or be proven for a specific concrete smooth `f`.
- "All functions" → "all smooth functions" is a real restriction; Wilson
  observables that are not smooth (rare but possible: indicator-like
  observables for cluster regions) would fall outside.

**Tier 2 axiom impact**: -1 (axiom retired, replaced by a theorem for the
smooth class).

### Option 3 — Sobolev / Dirichlet domain restriction

**Strategy**: define a Dirichlet domain `D(E)` and prove `LieDerivReg' f` for
`f ∈ D(E)`. This is the "natural" mathematical object for the log-Sobolev /
spectral-gap analytic content.

**Proposed Lean signature**:

```lean
def DirichletDomain (N_c : ℕ) [NeZero N_c] : Set (SUN_State_Concrete N_c → ℝ) :=
  { f | ∀ i U, DifferentiableAt ℝ (fun t => f (lieExpCurve … U t)) 0
        ∧ AEStronglyMeasurable (lieD' N_c i f) (sunHaarProb N_c)
        ∧ Integrable (fun U => (lieD' N_c i f U)^2) (sunHaarProb N_c) }

theorem lieDerivReg_of_dirichletDomain (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (hf : f ∈ DirichletDomain N_c) :
    LieDerivReg' N_c f
```

**Pros**:
- Most mathematically faithful: the Dirichlet domain is exactly the right
  function class for analytic Markov-semigroup / log-Sobolev work.
- Aligns with Mathlib's `SobolevSpace` / `Memℒp` machinery if/when it
  matures.
- Composable with the F3-MAYER blueprint downstream (Brydges-Kennedy needs
  L^∞ bounds on smooth fluctuations; Dirichlet domain is the natural carrier).

**Cons**:
- Refactor cost: highest. Defining `DirichletDomain`, proving closure under
  +, scalar mult, etc., is itself ~150-300 LOC.
- Effectively a stricter form of Option 1: the `LieDerivReg'` structure
  fields are exactly the `DirichletDomain` membership, so this option is
  largely a renaming exercise unless the analytic content of Dirichlet
  domain is genuinely needed.

**Tier 2 axiom impact**: -1.

---

## (c) Per-option downstream consumer impact

| Consumer | Option 1 (hypothesis) | Option 2 (smooth) | Option 3 (Dirichlet domain) |
|---|---|---|---|
| `lieD'_add` (LieDerivReg_v4:70) | takes `hf hg : LieDerivReg' N_c _` | takes `hf hg : ContDiff ℝ ⊤ _` (or uses `lieDerivReg_smooth` to derive `LieDerivReg'`) | takes `hf hg : _ ∈ DirichletDomain N_c` |
| `lieD'_smul` (LieDerivReg_v4:80) | takes `hf : LieDerivReg' N_c f` | takes `hf : ContDiff ℝ ⊤ f` | takes `hf : f ∈ DirichletDomain N_c` |
| `dirichletForm''_subadditive` (LieDerivReg_v4:94) | takes 3 hypotheses (`hf`, `hg`, `hfg`) explicitly | takes 3 `ContDiff` hypotheses; needs lemma `ContDiff.add` to derive `hfg` | takes 3 domain-membership hypotheses; needs `DirichletDomain.add` closure lemma |
| `sunDirichletForm_subadditive` (P8_PhysicalGap/SUN_DirichletCore:109) | takes 3 `LieDerivReg'` hypotheses | takes 3 `ContDiff` hypotheses + `ContDiff.add` | takes 3 domain-membership + `DirichletDomain.add` |
| GeneratorAxiomsDimOne.lean:56 (comment table) | comment update only; no math change | same | same |
| Tier 2 axiom count | 5 → 4 | 5 → 4 | 5 → 4 |
| New auxiliary theorems needed | 0 | 1 (`lieDerivReg_smooth`) | 2+ (`DirichletDomain` def + closure lemmas) |
| LOC delta | ~100 (signature + caller updates) | ~180 (~80 proof + ~100 callers) | ~250-400 (definition + closure + callers) |

**Key observation**: the active consumers (`lieD'_add`, `lieD'_smul`, both
`subadditive` theorems) need `LieDerivReg' f` *as input*. They do not care
how that input is produced. So **Option 1 makes them maximally generic** —
any future smoothness theorem or Dirichlet-domain theorem can supply the
input without further refactor.

---

## (d) Recommended option

**Cowork recommends Option 1 (eliminate the axiom; pass `LieDerivReg' f` as
explicit hypothesis)**, with Option 2 (`lieDerivReg_smooth`) filed as a
follow-up theorem.

### Justification

1. **Honest math**. Option 1 turns "lieDerivReg_all is true for all f" (false)
   into "lieD'_add is true for all f admitting LieDerivReg'" (true). The
   conditional structure of the math is now visible in the type signature.
2. **Lowest refactor cost** for the axiom retirement itself. ~100 LOC of
   signature changes; no new theorems required.
3. **Maximally composable**. Future work (Option 2 smooth theorem, Option 3
   Dirichlet domain, or a more specific physical-observables theorem) can
   each supply the `LieDerivReg' f` input separately. Option 1 is the
   foundation; Options 2 and 3 are followups that build on it.
4. **Anti-vacuity**. Currently the project's downstream `dirichletForm` /
   subadditivity theorems formally type-check by virtue of the false
   axiom. Option 1 makes this conditional structure explicit, which is the
   honest description of where the math actually stands.
5. **Tier 2 axiom count drops 5 → 4**.

### Filing convention

1. **Cowork audits** this scope document (next step: `COWORK-AUDIT-EXP-LIEDERIVREG-REFORMULATION-SCOPE-001` could be filed if needed; otherwise this audit-by-Cowork document is sufficient).
2. **Codex implements** Option 1 verbatim per §(b)/Option 1 + §(c)/per-consumer signatures. Estimated LOC: ~100. Anticipated Codex task: `CODEX-LIEDERIVREG-AXIOM-RETIRE-001` (priority 5; not blocking F3 work).
3. **Cowork audits the implementation** post-Codex: verify the axiom is gone, all 4 consumer theorems take the hypothesis explicitly, no new sorries, oracle-clean traces. Auto-promote `COWORK-AUDIT-CODEX-LIEDERIVREG-AXIOM-RETIRE-001` (FUTURE) when Codex marks DONE.
4. **Tier 2 count update**: LEDGER row "5 real declarations" → "4 real declarations" with Cowork freshness-audit-N+1 confirming the count drop.
5. **Optional Option 2 follow-up** (`CODEX-LIEDERIVREG-SMOOTH-THEOREM-001`, priority 7-8): prove `lieDerivReg_smooth` so consumers can use it for the dominant smooth-observable case without manual hypothesis discharge.

### Anti-overclaim invariants

- This scope document does NOT claim a reformulation has been proved.
- This scope document does NOT imply the existing INVALID axiom can be
  patched; the axiom must be **removed** in favour of an explicit
  hypothesis (Option 1) or a theorem on a smaller class (Option 2/3).
- F3-COUNT row remains `CONDITIONAL_BRIDGE`. F3-MAYER remains `BLOCKED`.
  This scope is independent of the F3 path.
- Tier 2 axiom count remains 5 until Codex implements Option 1.
- The downstream consumers' subadditivity theorems remain technically valid
  *only* by virtue of the false axiom; Option 1 makes their conditional
  structure honest.

---

## (e) Mathlib helpers cross-reference

For each option, Cowork pre-identified the Mathlib helpers Codex will need:

### Option 1 — no new helpers required

The `LieDerivReg'` structure already exists at `LieDerivReg_v4.lean:50`.
Hypothesis-passing is purely syntactic; no new Mathlib content needed.

### Option 2 — for proving `lieDerivReg_smooth`

| Mathlib helper | Use |
|---|---|
| `ContDiff.differentiable` | Smooth ⇒ differentiable everywhere; derive `.diff` field |
| `ContDiff.continuous` | Smooth ⇒ continuous; derive measurability via `Continuous.aestronglyMeasurable` |
| `Continuous.aestronglyMeasurable` | Continuous ⇒ AE strongly measurable; derive `.meas` field |
| `IsCompact.continuous_integrable` (or `MeasureTheory.IsCompact.integrableOn_isCompact_of_continuous`) | Continuous on compact ⇒ integrable; derive `.sq_int` via square-of-bounded-continuous |
| `Continuous.integrable_of_isCompact_support` (if applicable) | for compactly supported variant |
| `MeasureTheory.Memℒp` / `Lp` machinery | establish the `Integrable (fun U => ... ^ 2)` membership |

Codex pre-check before formalizing: grep Mathlib for
`Continuous.aestronglyMeasurable`, `ContDiff.continuous`,
`Continuous.integrable_of_isCompact`, and (for the SU(N) compact-group
side) `IsCompact (Set.univ : Set (specialUnitaryGroup ...))`.

### Option 3 — for `DirichletDomain` definition + closure lemmas

| Mathlib helper | Use |
|---|---|
| `MeasureTheory.MeasurableSpace.set` | for defining a `Set (functions)` |
| `MeasureTheory.AEStronglyMeasurable.add` | closure of `meas` field under + |
| `MeasureTheory.Integrable.add` | closure of `sq_int` under + (needs `(f+g)^2 ≤ 2 f^2 + 2 g^2` already in proof) |
| `DifferentiableAt.add` | closure of `diff` field under + |
| `DifferentiableAt.smul` | closure of `diff` field under scalar |
| `MeasureTheory.AEStronglyMeasurable.const_smul` | closure of `meas` under scalar |
| Possibly `Mathlib.Analysis.NormedSpace.lpSpace` for Sobolev-like type | if generalising to `H^1` |

If Option 3 is chosen, Cowork recommends a separate scoping pass to
identify whether Mathlib's nascent Sobolev / Dirichlet machinery is mature
enough to base the definition on, or whether the project should define
`DirichletDomain` as a simple `Set` with hand-rolled closure lemmas.

---

## Honesty discipline

- **This is a scope, not a proof.** Cowork has not proved any reformulation;
  filing this document does not move any LEDGER row.
- **The axiom must be REPLACED, not patched.** Option 1 deletes the
  `axiom lieDerivReg_all` line and replaces it with explicit hypotheses on
  consumers. Options 2 and 3 are alternative forms where the hypothesis is
  discharged for a specific function class.
- **F3-COUNT row** in `UNCONDITIONALITY_LEDGER.md`: unchanged
  (`CONDITIONAL_BRIDGE`).
- **F3-MAYER row**: unchanged (`BLOCKED`).
- **Tier 2 axiom count**: 5 (unchanged until Codex implements Option 1).
- **dashboard `unconditionality_status`**: `NOT_ESTABLISHED`.
- **All 4 percentages**: unchanged at 5% / 28% / 23-25% / 50%.
- **README badges**: unchanged.

The reformulation, if Codex implements Option 1, would drop the Tier 2
count from 5 to 4 — a real (if small) Tier 2 retirement that, unlike the
vacuous EXP-SUN-GEN retirement, is mathematically substantive (the
subadditivity theorems become **conditionally** true, which matches the
math).

## Cross-references

- `UNCONDITIONALITY_LEDGER.md:109` — EXP-LIEDERIVREG row, status
  `INVALID`, next action "Restrict to smooth f".
- `KNOWN_ISSUES.md` — currently has no §1.X entry on EXP-LIEDERIVREG; Cowork
  recommends filing one when Option 1 ships, citing this scope document.
- `LieDerivReg_v4.lean:50–55` — the `LieDerivReg'` structure (used as
  hypothesis carrier in Option 1).
- `LieDerivReg_v4.lean:58` — the INVALID axiom this document scopes the
  replacement of.
- `P8_PhysicalGap/SUN_DirichletCore.lean:109` — the consumer outside
  `Experimental/` that needs hypothesis-passing.
- `JOINT_AGENT_PLANNER.md` critical path step 4
  (`EXPERIMENTAL-AXIOM-CLASSIFICATION`) names this row as one of the
  experimental axioms to "retire, reformulate, or quarantine".
- `F3_COUNT_DEPENDENCY_MAP.md` and `F3_MAYER_DEPENDENCY_MAP.md` — the F3
  blueprints are independent of this reformulation; F3 progress does not
  block on EXP-LIEDERIVREG.

---

*End of EXP-LIEDERIVREG reformulation scope. Filed by Cowork as
deliverable for `COWORK-EXP-LIEDERIVREG-REFORMULATION-SCOPE-001` per
dispatcher instruction at 2026-04-26T19:15:00Z. Cowork is scoping, not
proving; the axiom must be replaced, not patched.*
