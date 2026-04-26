# vacuity_flag_column_draft.md

**Cowork-authored concrete spec for the `vacuity_flag` column on
`UNCONDITIONALITY_LEDGER.md` Tier 1 + Tier 2 tables.**
**Filed: 2026-04-26T18:25:00Z by Cowork.**
**Loop-closing input for `CODEX-VACUITY-RULES-CONSOLIDATION-001` /
`CODEX-VACUITY-RULES-CONSOLIDATION-FINISH-001` per
`REC-COWORK-VACUITY-FLAG-LEDGER-COLUMN-001` priority 2.**

This file is a Codex-ready spec. Codex implements the column verbatim from
sections (b) + (c) + (d). No design decisions are left to Codex; every Tier
1 + Tier 2 row already has a recommended `vacuity_flag` value with
justification and `KNOWN_ISSUES.md` cross-reference.

**Anti-overclaim invariant** (must hold across the whole implementation):
adding the column **must not** change any LEDGER row's `Status`,
`Dependency`, `Evidence`, or `Next action` cell. The `vacuity_flag` column
is a separate honesty annotation that lives alongside `Status` without
modifying it.

---

## (a) Seven enumerated values, with definition + example

The 7 values are copied verbatim from `UNCONDITIONALITY_LEDGER.md` §38
(lines 47–59 of the interim schema). Definitions are unchanged; this
section adds **one concrete example each** so a reviewer can disambiguate
borderline cases.

| Value | Definition | Concrete example |
|---|---|---|
| `none` | No known vacuity caveat. | `L1-HAAR` (Haar measure on SU(N), reusable representation theory) |
| `caveat-only` | Genuine formal content exists, but reviewers must read a caveat before interpreting the row externally. | `F3-COUNT` (CONDITIONAL_BRIDGE; v2.42–v2.54 progress is real, but the row is not closed) |
| `vacuous-witness` | The formal witness exists because the target proposition is weak, empty, or trivially inhabitable. | Clay weak endpoint canaries: `ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys` is satisfied by any positive real — the proposition is too weak to be physical content |
| `trivial-group` | The witness uses `SU(1)` or another degenerate group case and does not transfer to `SU(N)` for `N ≥ 2`. | `NC1-WITNESS` (`ClayYangMillsMassGap 1` for the trivial group `SU(1) = {1}`) |
| `zero-family` | The witness uses the zero object/family to satisfy shape predicates, without supplying the intended nonzero spanning/basis data. | `EXP-SUN-GEN` (`generatorMatrix := 0`; satisfies the skew-Hermitian + trace-zero shape but is not a Pauli/Gell-Mann basis) |
| `anchor-structure` | The row proves scaffolding or carrier shape, not the analytic content that external readers may expect. | OS-style structural axioms inhabited at SU(1) (Finding 011); Bałaban predicate carriers (Findings 013-014) |
| `trivial-placeholder` | The row is a placeholder or bookkeeping endpoint whose inhabitant should not be described as mathematical progress. | `CONTINUUM-COORDSCALE` (architectural rescaling trick, marked `INVALID-AS-CONTINUUM`) |

**Default value for new rows**: `none`. Codex must not assign any other
value without explicit Cowork audit.

---

## (b) Proposed column header markdown

For both Tier 1 and Tier 2 tables, the new column slots **as the second-to-last
column**, immediately before `Next action`. Header row:

### Tier 1 (current 6 columns → new 7 columns)

```markdown
| ID | Claim | Status | Dependency | Evidence | vacuity_flag | Next action |
|---|---|---|---|---|---|---|
```

### Tier 2 (current 5 columns → new 6 columns)

```markdown
| ID | Claim | Status | Retire effort | vacuity_flag | Next action |
|---|---|---|---|---|---|
```

**Why second-to-last**: keeping `Next action` in the rightmost column
preserves the existing reading flow (left-to-right: identifier → claim
→ verification status → what to do next). Inserting `vacuity_flag`
just before `Next action` keeps it visually adjacent to the `Status` /
`Evidence` cells it qualifies, which matches the §38 interim schema's
"honesty annotation" framing.

**Tier 0 + Tier 3 (out of scope for this draft)**: Tier 0 rows
(CLAY-GOAL, AGENTIC-INFRA, AUTOCONTINUE, JOINT-PLANNER) and Tier 3
rows (OUT-CONTINUUM, OUT-OS-WIGHTMAN, OUT-STRONG-COUPLING) are
infrastructure / outside-scope and do not need the column at this
stage. If they are added later, all four Tier 0 rows are `none` and
all three Tier 3 rows are `none` (their `BLOCKED` status is not a
vacuity issue).

---

## (c) Per-row recommended `vacuity_flag` for every Tier 1 + Tier 2 row

Read against `UNCONDITIONALITY_LEDGER.md` lines 88–111 (current Tier 1 +
Tier 2 tables, post-v2.54.0). Every row of the current LEDGER has a
recommended value. **No row's `Status` is changed.**

### Tier 1 — Lattice mass gap (active formalization scope)

| ID | Recommended vacuity_flag | Justification | KNOWN_ISSUES.md cross-reference |
|---|---|---|---|
| `L1-HAAR` | `none` | Real Haar measure on SU(N), Mathlib-foundational, reusable in any continuum proof. No vacuity caveat known. | n/a (no caveat) |
| `L2.4-SCHUR` | `none` | Real Schur orthogonality scaffolding for matrix coefficients. Mathematically substantive. | n/a |
| `L2.5-FROBENIUS` | `none` | Real Frobenius trace bound `∑ ∫ |U_ii|² ≤ N`. Substantive. | n/a |
| `L2.6-CHARACTER` | `none` | Real character inner product `∫ |tr U|² dμ = 1`. Substantive; the central L1 → L2 interface. | n/a |
| `F3-ANCHOR-SHELL` | `none` | Real anchored root shell with bounded + injective code; v2.42–v2.44 lattice-animal infrastructure. Substantive combinatorics. | n/a |
| `F3-COUNT` | `caveat-only` | CONDITIONAL_BRIDGE. v2.48 + v2.50 + v2.51 + v2.52 + v2.53 + v2.54 deliver real graph-theoretic progress, but the row is not closed: the global root-avoiding safe-deletion theorem and full anchored word decoder are still pending. External readers must not interpret as F3-COUNT closed. | n/a (no vacuity, but caveat needed for status) |
| `F3-MAYER` | `none` | BLOCKED. No formal artifact yet. Not vacuous; just not started pending F3-COUNT closure. | n/a |
| `F3-COMBINED` | `none` | BLOCKED. Mechanical assembly skeleton only; not vacuous. | n/a |
| `NC1-WITNESS` | `trivial-group` | `ClayYangMillsMassGap 1` is oracle-clean but uses SU(1) = {1}, which is the trivial group. Connected correlator vanishes identically; ConnectedCorrDecay holds vacuously. Does not transfer to SU(N), N ≥ 2. | §1.1 (NC1-WITNESS unconditional witness) + §9 Finding 011 (SU(1) OS-style structural axioms) |
| `CONTINUUM-COORDSCALE` | `trivial-placeholder` | Marked `INVALID-AS-CONTINUUM`; the "continuum mass gap via coordinated scaling" is an architectural rescaling trick, not analysis. Must not be counted as continuum-limit progress. | §1.2 (`ClayYangMillsPhysicalStrong` reached via coordinated scaling) + Finding 004 |

### Tier 2 — Experimental axioms (5 real declarations in `Experimental/`)

| ID | Recommended vacuity_flag | Justification | KNOWN_ISSUES.md cross-reference |
|---|---|---|---|
| `EXP-SUN-GEN` | `zero-family` | "Retired" by `generatorMatrix := 0`. Zero matrix is skew-Hermitian and trace-zero, so it satisfies the shape predicates `gen_skewHerm` and `gen_trace_zero`, but it is **not** a Pauli/Gell-Mann/general `su(N)` generator basis. The retirement is structurally honest but vacuous on physics. | §1.3 (EXP-SUN-GEN axiom retirement is technically valid but vacuous) |
| `EXP-MATEXP-DET` | `none` | Real Mathlib-level theorem `Matrix.det_exp_eq_exp_trace_fin_one`. Built locally at Mathlib commit `cd3b69baae` with no `sorry` and pinned `#print axioms`. Publication blocked on GitHub auth, not on mathematical content. | n/a (substantive Mathlib lemma) |
| `EXP-LIEDERIVREG` | `caveat-only` | INVALID **as currently stated** — `lieDerivReg_all` is mathematically false in its current "all functions" form. The row genuinely needs reformulation (restrict to smooth `f`); meanwhile, *no proof depending on this axiom is sound*. The caveat-only flag captures "real Lean axiom but the proposition is wrong"; the `Status: INVALID` cell already disqualifies the row from honest use. | §1.X (any future entry on EXP-LIEDERIVREG reformulation; currently captured at LEDGER:109 status column) |
| `EXP-BAKRYEMERY-SPIKE` | `caveat-only` | EXPERIMENTAL with classification pending: `sun_haar_satisfies_lsi` may be a live spike or an archive remnant. Until classification (per `REC-COWORK-BAKRYEMERY-SPIKE-CLASSIFY-001`) the row needs a reviewer caveat; not strictly vacuous, but not yet certified live. | n/a (pending classification) |
| `EXP-BD-HY-GR` | `caveat-only` | EXPERIMENTAL; 2 real declarations (`variance_decay_from_bridge_and_poincare_semigroup_gap`, `gronwall_variance_decay`). Hard Mathlib infrastructure gap; not vacuous, but external readers must not interpret as proven. | n/a (long-tail Mathlib infrastructure) |

### Vacuity-pattern instances tracked outside current LEDGER rows

The following instances are documented in `KNOWN_ISSUES.md` §9 + §10.3 +
`COWORK_FINDINGS.md` Findings 011–016 but do **not** correspond to a
first-class Tier 1 or Tier 2 LEDGER row at the time of this draft. The
LEDGER §38 interim schema bundles them as a single line ("Bałaban / OS-style
structural carriers mentioned in `KNOWN_ISSUES.md` §9").

When the full per-row column is added, **Cowork recommends** that Codex also
introduce **new LEDGER rows** (or note them inline in the Tier 1 evidence
column) so each pattern has its own `vacuity_flag`. Below is the
recommended row inventory:

| Proposed row ID (or location to inline) | Pattern | Recommended vacuity_flag | Justification | KNOWN_ISSUES.md cross-reference |
|---|---|---|---|---|
| `OS-AXIOM-SU1` (new Tier 1 row, or inline note on `NC1-WITNESS`) | SU(1) OS-style structural axioms (`OSCovariant`, `OSReflectionPositive`, `OSClusterProperty`, `HasInfiniteVolumeLimit`) admitting unconditional inhabitants | `anchor-structure` | Carrier inhabitation does not supply the analytic Wightman/Osterwalder-Schrader content the names suggest. Vacuous on N ≥ 2. | §9 Finding 011 |
| `BRANCH-III-PREDICATES` (new Tier 1 row) | Branch III analytic predicate set (LSI, Poincaré, clustering, Dirichlet form, Markov-semigroup, Feynman-Kac bridge) inhabited at SU(1) | `anchor-structure` | Predicate inhabitation at SU(1); same caveat as Finding 011 extends. | §9 Finding 012 |
| `BALABAN-CARRIERS` (new Tier 1 row) | Bałaban predicate carriers (`BalabanHyps`, `WilsonPolymerActivityBound`, `LargeFieldActivityBound`, `SmallFieldActivityBound`) trivially inhabitable for every `N_c ≥ 1` | `anchor-structure` | Carriers inhabited via zero/identity/vacuous witnesses; genuine analytic content lives outside the carriers. | §9 Findings 013–014 |
| `BALABAN-RG-SCAFFOLD` (new Tier 1 row) | Codex BalabanRG/ push (~222 files, 0 sorries, 0 axioms) scaffolding the entire Branch II chain to `ClayYangMillsTheorem` with trivial-witness placeholders | `anchor-structure` | `RGContractionRate.lean` lines 70–82 explicitly note the trivial witnesses must be upgraded to genuine RG dynamics. Carrier-only progress. | §9 Finding 015 |
| `CLAY-CORE-LSI` (new Tier 1 row) | `ClayCoreLSI` is an arithmetic existential triviality, not the integral form of LSI. Substantive content concentrated in `ClayCoreLSIToSUNDLRTransfer d N_c` for `N_c ≥ 2`. | `vacuous-witness` (for the `ClayCoreLSI` predicate itself); the transfer structure deserves its own row with `caveat-only` once landed | The named predicate is trivially inhabited; substance lives in the bridge to `DLR_LSI`. | §9 Finding 016 |
| `TRIPLE-VIEW-L42-L43-L44` (new Tier 1 row) | Triple-view characterisation (L42 + L43 + L44) structurally complete but substantively empty; inputs `c_Y`, `c_σ`, `ω ≠ 1` are anchor structures, NOT derived from first principles | `anchor-structure` | Structural plumbing only; not derived. | §10.3 |
| `CLAY-WEAK-ENDPOINT` (new Tier 1 row, or inline on `NC1-WITNESS`) | Clay weak endpoint canaries (`ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys`) | `vacuous-witness` | The proposition is satisfied by any positive real; trivially inhabited by the SU(1) witness. Useful audit tripwire only. | §1.1 + §9 Finding 015 (canaries appear adjacent to BalabanRG scaffold) |

**Cowork-VACUITY-PATTERN-TRACKER-001 audit cross-check**: this draft
explicitly enumerates **all 7+ vacuity-pattern instances** identified in
that earlier audit. Stop condition (b) of `COWORK-VACUITY-FLAG-COLUMN-DRAFT-001`
("a vacuity-pattern instance from Findings 011-016 + §10.3 is missing") is
**NOT TRIGGERED**: §1.1 + §1.2 + §1.3 + §9 Findings 011/012/013-014/015/016
+ §10.3 + Clay weak endpoint canaries are all covered (with explicit
recommendations either as a flag on an existing LEDGER row or as a
proposed new row).

---

## (d) Insertion instructions for Codex

This section gives Codex a step-by-step recipe to land the column verbatim
from sections (b) + (c). All instructions are mechanical; no design choices
are left open.

### D.1 Tier 1 table edit

**File**: `UNCONDITIONALITY_LEDGER.md`, current lines 90–101 (subject to
small drift if the LEDGER has been touched since this draft).

**Step**: rewrite the Tier 1 header at line 90 as:

```markdown
| ID | Claim | Status | Dependency | Evidence | vacuity_flag | Next action |
|---|---|---|---|---|---|---|
```

(seven `|` separators per row). Adjust the column-alignment row at line 91
to add one more `|---|`.

**Then** for each existing Tier 1 row (lines 92–101), insert one new cell
between `Evidence` and `Next action` containing the recommended
`vacuity_flag` value from §(c) above. Specifically, in left-to-right
order of LEDGER lines:

| LEDGER line | Row ID | Insert cell content |
|---:|---|---|
| 92 | L1-HAAR | `none` |
| 93 | L2.4-SCHUR | `none` |
| 94 | L2.5-FROBENIUS | `none` |
| 95 | L2.6-CHARACTER | `none` |
| 96 | F3-ANCHOR-SHELL | `none` |
| 97 | F3-COUNT | `caveat-only` |
| 98 | F3-MAYER | `none` |
| 99 | F3-COMBINED | `none` |
| 100 | NC1-WITNESS | `trivial-group` |
| 101 | CONTINUUM-COORDSCALE | `trivial-placeholder` |

### D.2 Tier 2 table edit

**File**: same, current lines 105–111.

**Step**: rewrite the Tier 2 header at line 105 as:

```markdown
| ID | Claim | Status | Retire effort | vacuity_flag | Next action |
|---|---|---|---|---|---|
```

(six `|` separators per row).

**Then** for each existing Tier 2 row (lines 107–111), insert one new cell
between `Retire effort` and `Next action`:

| LEDGER line | Row ID | Insert cell content |
|---:|---|---|
| 107 | EXP-SUN-GEN | `zero-family` |
| 108 | EXP-MATEXP-DET | `none` |
| 109 | EXP-LIEDERIVREG | `caveat-only` |
| 110 | EXP-BAKRYEMERY-SPIKE | `caveat-only` |
| 111 | EXP-BD-HY-GR | `caveat-only` |

### D.3 LEDGER §38 interim schema cleanup

After D.1 + D.2 land, the LEDGER §38 5-row interim applications table
(lines 63–69) is **superseded** by the per-row column. Codex should:

- Replace the §38 "Current known applications before the full column
  migration" subsection with a one-paragraph note pointing to the new Tier
  1 + Tier 2 columns and to this draft document
  (`dashboard/vacuity_flag_column_draft.md`).
- Keep §38's enum definitions (lines 47–59) — they remain the authoritative
  schema reference.
- Update §38's "Implementation note" (lines 71–75) to read "Full Tier 1 +
  Tier 2 column delivered on 2026-04-26 per
  `dashboard/vacuity_flag_column_draft.md`."

### D.4 Optional follow-up (NOT part of CODEX-VACUITY-RULES-CONSOLIDATION-001)

If the project decides to promote the §9 + §10.3 vacuity-pattern instances
from `KNOWN_ISSUES.md` to first-class LEDGER rows (recommended in §(c)
above), Codex should file a separate task `CODEX-LEDGER-VACUITY-PATTERN-ROWS-001`
to add the 7 proposed rows enumerated in §(c)'s third table. **Do not bundle
this follow-up into the present consolidation task** — it would change LEDGER
row count, which is structurally distinct from adding a column.

### D.5 Row-spanning entries

The current Tier 1 + Tier 2 tables have **no** row-spanning entries. Each
row occupies one logical row of the markdown table. No special handling is
needed.

If a future Tier 1 row needs to wrap (e.g. F3-COUNT's evidence column has
become long), the wrap should be handled by leaving the cell on a single
markdown line with embedded `<br>` tags or by a continuation-line
convention — but the `vacuity_flag` cell itself is always a single
identifier from the §(a) enum.

### D.6 Verification after insertion

After landing D.1 + D.2, Codex verifies by:

1. `grep "^|" UNCONDITIONALITY_LEDGER.md | head -n 100` — every Tier 1 +
   Tier 2 row now has 7 (Tier 1) or 6 (Tier 2) `|` separators.
2. `grep "vacuity_flag" UNCONDITIONALITY_LEDGER.md` — should match the new
   Tier 1 header + new Tier 2 header + the §38 enum-definition section
   (line 38).
3. Spot-check that **no row's Status / Dependency / Evidence / Next action
   cell text changed** from the pre-D.1 state. (Diff before/after; only
   inserted `vacuity_flag` cells should differ.)

After verification, file a `task_done` event for `CODEX-VACUITY-RULES-CONSOLIDATION-001`
and the auto-promote trigger for `COWORK-AUDIT-CODEX-VACUITY-CONSOLIDATION-001`
fires.

---

## Honesty discipline

- This draft is a **specification**, not a proof or a math advance. Filing
  it does not move any LEDGER row.
- Every `vacuity_flag` value in §(c) is an honesty annotation on the row's
  *interpretation*, not on its formal proof status. The `Status` column
  (`FORMAL_KERNEL`, `CONDITIONAL_BRIDGE`, `INVALID`, etc.) is unchanged.
- The 7 proposed new rows in §(c)'s third table are **recommendations**,
  not part of the present `CODEX-VACUITY-RULES-CONSOLIDATION-001` task.
  Following them up requires a separate `CODEX-LEDGER-VACUITY-PATTERN-ROWS-001`
  task per §(d)/D.4.
- After Codex implements §(d)/D.1–D.3, the LEDGER will have a clean,
  per-row honesty annotation column without any silent row mutations. The
  external-reader vocabulary expands from 8 status labels to 8 status
  labels × 7 vacuity flags, but the math content is unchanged.
- If any reviewer (Cowork or external) detects that a `vacuity_flag` value
  in §(c) is wrong (e.g. a row should be `none` but is flagged
  `caveat-only`, or vice versa), the correction should be filed as a
  **Cowork audit** of the column, not a Codex commit on top of this draft.
  This preserves separation of concerns: Cowork curates the honesty
  annotations; Codex implements.

---

## Cross-references

- `UNCONDITIONALITY_LEDGER.md` §38 (lines 38–75) — interim schema with the
  same 7-value enum and a 5-row applications table that this draft
  supersedes.
- `MATHEMATICAL_REVIEWERS_COMPANION.md` §3.3 (lines 115–147) — reviewer-facing
  explanation that complements the LEDGER column.
- `KNOWN_ISSUES.md` §1.1, §1.2, §1.3, §9 Findings 011–016, §10.3 — source
  of all documented vacuity patterns.
- `COWORK_FINDINGS.md` Findings 011–016 — primary references.
- `registry/recommendations.yaml` `REC-COWORK-VACUITY-FLAG-LEDGER-COLUMN-001`
  (priority 2, OPEN) — recommendation this draft fulfils.

---

*End of vacuity_flag column draft. Filed by Cowork as deliverable for
`COWORK-VACUITY-FLAG-COLUMN-DRAFT-001` per dispatcher instruction at
2026-04-26T18:20:00Z. Codex-ready spec; verbatim implementation.*
