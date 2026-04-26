# CLAY_HORIZON.md

**Cowork-authored honest external-reader companion for the Clay scope.**
**Originally filed: 2026-04-26T17:30:00Z. Refreshed: 2026-04-26T20:35:00Z (post-v2.57.0) per `COWORK-CLAY-HORIZON-REFRESH-001`.**
**Status of CLAY-GOAL in `UNCONDITIONALITY_LEDGER.md`: `BLOCKED`. Global
unconditionality status: `NOT_ESTABLISHED`.**

**Refresh summary (20:35Z)**: since this document was first filed at 17:30Z,
the project has accumulated significant new context but **no LEDGER row has
moved and no percentage has changed**. F3-COUNT progressed v2.52 → v2.53 →
v2.54 → v2.55 → v2.56 → v2.57 (5 narrow increments since this document's
first filing) — F3-COUNT row stayed `CONDITIONAL_BRIDGE` through every one.
Three new Cowork deliverables landed: `F3_MAYER_DEPENDENCY_MAP.md`,
`dashboard/exp_liederivreg_reformulation_options.md`,
`dashboard/mayer_mathlib_precheck.md`. Six Cowork-filed recommendations were
resolved. The lattice 28% / Clay-as-stated 5% / honesty-discounted 23–25% /
named-frontier 50% headline numbers are unchanged. **The OUT-* rows
(continuum / OS-Wightman / strong coupling) remain BLOCKED. The honest growth
ceiling for Clay-as-stated remains ~10–12% even after full F3-* lattice
closure.**

This document exists because the LEDGER's Tier 0 / Tier 1 rows show several
`FORMAL_KERNEL` entries (Haar measure on SU(N), Schur orthogonality, the
character inner product), and an external reader landing on the README's
50% named-frontier badge could plausibly walk away thinking the project is
"halfway to the Clay Yang-Mills Mass Gap problem." That is **not** what the
percentages mean. This document explains, honestly, what the project is
formalising, what it is not formalising, and how far each component is
from the literal Clay target.

It is a planning / honesty instrument. It is not a proof. It does not move
any LEDGER row. The companion machine-readable percentages live in
`registry/progress_metrics.yaml`; the README badges (Clay-as-stated 5 %,
lattice small-β 28 %, named-frontier 50 %) and `JOINT_AGENT_PLANNER.md`
are the canonical numerical sources.

---

## (i) What this repository is formalising — and what it is not

**This repository is formalising**: the *lattice* mass gap for SU(N) gauge
theory at *small inverse coupling* β (concretely β < 1/(28 N_c); for QCD
N_c = 3 this means β < 1/84 ≈ 0.012). The mathematical content is

- representation theory of SU(N) (L1 Haar + L2.4–L2.6 Schur / Frobenius /
  character inner product),
- combinatorial counting of lattice animals (F3-COUNT, Klarner-style
  bound `count(n) ≤ K^n` for `K = 2d − 1`),
- random-walk / cluster-expansion bounds (F3-MAYER, Brydges-Kennedy /
  Mayer / Ursell), and
- final assembly into a small-β lattice gap (F3-COMBINED, conditional on
  the named hypotheses in `AXIOM_FRONTIER.md`).

**This repository is NOT formalising**: the *literal* Clay Millennium
Prize problem. The Clay statement requires:

1. A construction of *continuum* quantum Yang-Mills theory on R⁴ (the
   limit `a → 0` of the lattice theory; equivalent at the level of
   correlation functions to Osterwalder-Schrader / Wightman axioms).
2. A *positive mass gap* in that continuum theory for SU(N), N ≥ 2.
3. The mass gap holding for *all* values of the coupling, not only in the
   small-β regime where cluster expansion converges.

Items 1, 2, 3 correspond to LEDGER rows `OUT-CONTINUUM`, `OUT-OS-WIGHTMAN`,
`OUT-STRONG-COUPLING` respectively. All three are `BLOCKED`. The project
does not currently attack any of them.

The internal "small-β lattice mass gap" is a non-trivial sub-result that
*would* be a real ingredient in any serious continuum proof. But it is
strictly weaker than Clay-as-stated, and *no quantity of work on the
lattice side alone closes the Clay statement*. That's the central honesty
point this document exists to make.

A reader interested in Clay-as-stated should read this entire document
before drawing any conclusion about distance-to-Clay from the LEDGER or
the README badges.

---

## (ii) Per-row status of the three Clay-blocking OUT-* entries

All three rows live in Tier 3 ("Outside-current-scope items") of
`UNCONDITIONALITY_LEDGER.md` (lines 74–80). Their status is `BLOCKED`.
This section restates each blocker concretely, gives an honest distance
estimate, and lists what concrete formal infrastructure would have to
land before the row could move toward `READY` or `CONDITIONAL_BRIDGE`.

### OUT-CONTINUUM — continuum limit `a → 0` via Balaban RG to convergence

| Field | Value |
|---|---|
| LEDGER status | `BLOCKED` (`UNCONDITIONALITY_LEDGER.md:78`) |
| Mathematical content | A renormalization-group argument (Bałaban / Magnen-Rivasseau-Sénéor-style block-spin RG with non-perturbative bounds, or a ULTRAVIOLET cluster expansion adapted to gauge fields) showing that as the lattice spacing `a → 0`, the lattice Schwinger functions converge to a non-trivial limit satisfying the OS axioms |
| Concrete blocker | (a) Balaban RG is a multi-decade research-level project (Bałaban's original 1980s–1990s programme alone is ~30 years of papers, still partial); (b) Mathlib has no infrastructure for renormalization, block-spin transformations, or polymer expansions in the gauge-invariant sense; (c) the project's `BalabanRG/` files exist but are predicate-carrier scaffolding with trivial-witness placeholders (see KNOWN_ISSUES §9 / Findings 013-015), not actual analytic content |
| Distance estimate | **5+ years**, possibly multi-decade. This is a stand-alone research programme. Constructive QFT specialists treat this as the hardest part of the Clay problem |
| Concrete formal infrastructure that must land first | (1) Mathlib gauge-invariant function-space measures; (2) Mathlib renormalization-group / block-spin formalism; (3) project-side honest analytic content for Bałaban predicates (currently vacuous per Finding 014); (4) UV cluster expansion convergence proof in Lean |
| Cross-references | `KNOWN_ISSUES.md` §1.2 (CONTINUUM-COORDSCALE marked INVALID-AS-CONTINUUM); §9 / Findings 013–015 (BalabanRG vacuity); `CONTINUUM-COORDSCALE` row at LEDGER line 62 marked `INVALID-AS-CONTINUUM` |

### OUT-OS-WIGHTMAN — Osterwalder-Schrader / Wightman reconstruction

| Field | Value |
|---|---|
| LEDGER status | `BLOCKED` (`UNCONDITIONALITY_LEDGER.md:79`) |
| Mathematical content | The classical Osterwalder-Schrader theorem: given Schwinger functions satisfying OS0 (regularity), OS1 (Euclidean covariance), OS2 (reflection positivity), OS3 (symmetry), OS4 (cluster), reconstruct a relativistic quantum field theory satisfying the Wightman axioms — for *gauge* theories with *non-abelian* gauge group SU(N), N ≥ 2 |
| Concrete blocker | (a) OS reconstruction for non-abelian gauge theory is genuinely harder than for scalar field theories: gauge-fixing artifacts, BRST symmetry, and unitarity in physical Hilbert space all enter; (b) Mathlib has no Osterwalder-Schrader machinery and no Wightman-axiom infrastructure; (c) the project's `L9_OSReconstruction/` and `L6_OS/AbelianU1OSAxioms.lean` files handle only the abelian SU(1) case (see KNOWN_ISSUES §1.1 + Finding 011), which is the trivial group and gives no information about N ≥ 2 |
| Distance estimate | **Indeterminate, multi-year.** Strongly coupled to OUT-CONTINUUM: the OS axioms can only be checked once a continuum theory exists. Even granting OUT-CONTINUUM, the gauge-theory adaptation of OS reconstruction itself is a separate research-level project |
| Concrete formal infrastructure that must land first | (1) Mathlib Schwartz-distribution / tempered-distribution machinery for Schwinger functions; (2) Mathlib Wightman-axiom formalism; (3) project-side OS reconstruction for non-abelian gauge groups (currently only abelian/SU(1) handled, which is vacuous on physics); (4) gauge-invariant Hilbert space construction with BRST cohomology |
| Cross-references | `KNOWN_ISSUES.md` §1.1 (NC1-WITNESS / SU(1) trivial-group caveat); §9 / Finding 011 (SU(1) OS-style structural axioms vacuous for N ≥ 2); `NC1-WITNESS` row at LEDGER referenced as `FORMAL_KERNEL (with vacuity caveat per Finding 003)` |

### OUT-STRONG-COUPLING — mass gap at β > β_c (strong coupling)

| Field | Value |
|---|---|
| LEDGER status | `BLOCKED` (`UNCONDITIONALITY_LEDGER.md:80`) |
| Mathematical content | A mass gap result for SU(N) lattice gauge theory at all `β`, not just the small-β regime where cluster expansion converges. The Clay problem implicitly requires this because the physical continuum limit involves taking `β → ∞` along a renormalization-group trajectory, far outside the small-β regime |
| Concrete blocker | (a) Cluster / polymer expansions diverge for `β > β_c ≈ 1/(28 N_c)`; the project's whole F3-MAYER / Brydges-Kennedy machinery does not apply; (b) different techniques are required (chessboard estimates, transfer-matrix spectral analysis, large-N expansions, lattice-spin correlation inequalities), none of which the project formalises; (c) Mathlib has none of these alternative tools |
| Distance estimate | **Indeterminate, multi-year.** This is an open mathematical problem in its own right: there is no known unconditional proof of a mass gap at all couplings for non-abelian lattice gauge theory in any standard mathematical framework, even informally. Most expected approaches (e.g. through renormalization to the continuum) couple back to OUT-CONTINUUM |
| Concrete formal infrastructure that must land first | (1) Either a strong-coupling-friendly proof technique formalised in Mathlib (chessboard estimates, transfer matrix spectral analysis, spin-correlation inequalities for non-abelian groups); or (2) a continuum proof via OUT-CONTINUUM that bypasses the lattice strong-coupling question. Neither route is currently formalised |
| Cross-references | None — this row is honestly orthogonal to the F3-COUNT / F3-MAYER / F3-COMBINED chain the project is currently working on |

### Honourable mention — CONTINUUM-COORDSCALE (INVALID-AS-CONTINUUM)

| Field | Value |
|---|---|
| LEDGER status | `INVALID-AS-CONTINUUM` (`UNCONDITIONALITY_LEDGER.md:62`) |
| Why mentioned | Earlier project iterations had a row called `CONTINUUM-COORDSCALE` that *appeared* to provide a continuum bridge via coordinated scaling. Cowork Finding 004 + KNOWN_ISSUES.md §1.2 established that this is an architectural trick (rescaling lattice variables) not a real analytic continuum limit. External readers should NOT count this row as progress toward `OUT-CONTINUUM` |

---

## (iii) Honest "% toward Clay-as-stated" vs "% toward lattice mass gap"

The 4 percentages in `registry/progress_metrics.yaml` and the README badges
encode different things. This section repeats the Cowork-authored 16:35Z
dual-number answer with explicit per-row accounting and the obligatory
disclaimer.

### Disclaimer (mandatory, must accompany any % toward Clay-as-stated quote)

> **The Clay Millennium Prize problem requires a continuum quantum
> Yang-Mills theory on R⁴ with positive mass gap, satisfying the
> Osterwalder-Schrader / Wightman axioms, for SU(N), N ≥ 2, at all
> couplings.** This repository does **not** currently formalise the
> continuum theory. Three of the dominant Clay obstacles —
> `OUT-CONTINUUM`, `OUT-OS-WIGHTMAN`, `OUT-STRONG-COUPLING` — are all
> `BLOCKED` in `UNCONDITIONALITY_LEDGER.md`. Therefore any "% toward
> Clay-as-stated" estimate is necessarily small (≈ 5%) regardless of how
> much progress is made on the small-β lattice subgoal. **No amount of
> small-β lattice work alone closes the Clay statement.**

### Two distinct metrics, side by side

| Metric | Current estimate | What it measures |
|---|---:|---|
| Clay-as-stated | **~5 %** | Distance to a complete unconditional proof of the literal Clay statement (continuum, OS/Wightman, all β) |
| Lattice small-β mass gap (working subgoal) | **~28 %** | Distance to a complete unconditional formalisation of the lattice mass gap at β < 1/(28 N_c), which is what the project is actually building |
| Lattice small-β, honesty-discounted | **~23–25 %** | Same target as above with vacuous / low-content retirements (NC1-WITNESS, EXP-SUN-GEN; see KNOWN_ISSUES §1.1, §1.3) discounted out |
| Named-frontier retirement | **50 %** | Internal monotone metric counting retired entries in `AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`. Useful for internal pacing; **not** the literal Clay percentage |

### Per-row contribution table (with no row promoted)

This table reuses `registry/progress_metrics.yaml` component contributions
(audited at 17:00Z under `COWORK-AUDIT-JOINT-PLANNER-001` AUDIT_PASS).
**No row in this table has been promoted relative to the LEDGER**.

| Component | LEDGER status | Contribution to lattice 28 % | Contribution to Clay-as-stated 5 % |
|---|---|---:|---:|
| L1-HAAR | FORMAL_KERNEL (98%) | ~7.8 % | ~1 % (representation theory is reusable in any continuum proof) |
| L2.4-SCHUR | FORMAL_KERNEL (100%) | ~4 % | ~0.5 % (same) |
| L2.5-FROBENIUS | FORMAL_KERNEL (100%) | ~4 % | ~0.5 % (same) |
| L2.6-CHARACTER | FORMAL_KERNEL (100%) | ~4 % | ~0.5 % (same) |
| F3-COUNT | CONDITIONAL_BRIDGE (v2.48 + v2.50 + v2.51 + v2.52 + v2.53 + v2.54 + v2.55 + v2.56 + v2.57, ~35%; next math step is closing `PlaquetteGraphAnchoredTwoNonCutExists` for k ≥ 3 per `F3_COUNT_DEPENDENCY_MAP.md`) | ~5 % | ~0 % (lattice-combinatorics; does not apply at strong coupling or continuum) |
| F3-MAYER | BLOCKED on F3-COUNT | 0 % | 0 % |
| F3-COMBINED | BLOCKED on F3-COUNT + F3-MAYER | 0 % | 0 % |
| EXP-MATEXP-DET | EXPERIMENTAL (~40%) | ~1.5 % | ~0 % (technical Mathlib lemma, low Clay leverage) |
| EXP-BD-HY-GR | EXPERIMENTAL hard Mathlib gaps | ~0.7 % | ~0 % |
| EXP-LIEDERIVREG | INVALID (mathematically false as stated) | 0 % | 0 % |
| NC1-WITNESS | FORMAL_KERNEL **vacuous** | ~0 % honest | 0 % (SU(1) is the trivial group; no information about SU(N), N ≥ 2) |
| EXP-SUN-GEN | FORMAL_KERNEL **vacuous** | ~0 % honest | 0 % (zero matrix family) |
| INFRA-HYGIENE (dispatcher, ledger freshness, audit cadence) | INFRA_AUDITED | ~1 % | ~0 % |
| **OUT-CONTINUUM** | **BLOCKED** | **N/A — outside lattice scope** | **~0 % (dominant Clay obstacle)** |
| **OUT-OS-WIGHTMAN** | **BLOCKED** | **N/A — outside lattice scope** | **~0 % (dominant Clay obstacle)** |
| **OUT-STRONG-COUPLING** | **BLOCKED** | **N/A — outside lattice scope** | **~0 % (dominant Clay obstacle)** |
| **Total** | | **~28 %** | **~5 %** |

### Why the Clay-as-stated row only adds up to ~5 %

The L1 / L2.4–L2.6 rows are *reusable infrastructure* that any continuum
proof would also need; we generously estimate they contribute ~2.5 %
toward Clay-as-stated as foundational representation theory. The
remaining ~2.5 % is sweat-of-effort credit for having the formalisation
discipline and tooling in place. The three OUT-* rows together account
for ~95 % of the Clay-as-stated picture and they are all BLOCKED. There
is no honest path to a higher Clay-as-stated number from purely
lattice-side work.

### Why the named-frontier 50 % is not the Clay percentage

The 50 % named-frontier number measures retirement of named entries in
`AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`. Those frontiers are scoped to
the project's internal mass-gap chain (L1 / L2 / L3 with declared physics
hypotheses). They do not include the OUT-* rows because those rows are
not in the project's active formal chain. Quoting 50 % "toward Clay" is a
category error; quoting 50 % "named-frontier retirement" is the honest
shape.

### Honest growth ceiling

Even if the project closes everything in the lattice 28 % column today,
the Clay-as-stated number stops at ~10–12 % until at least *one* of the
three OUT-* rows becomes a CONDITIONAL_BRIDGE. The next Clay-as-stated
percentage move requires either (a) Mathlib gauge-theory infrastructure
landing (continuum measures, Wightman axioms, OS reconstruction
machinery) — multi-year horizon; or (b) a concrete blueprint for one of
the OUT-* rows formalised in this repository — also multi-year, and
requires substantial new mathematical content beyond what the cluster
expansion provides.

---

## (iv) Cross-references to KNOWN_ISSUES vacuity caveats

External readers reading the LEDGER without consulting `KNOWN_ISSUES.md`
risk *double-counting* vacuous FORMAL_KERNEL rows — i.e., treating
trivial-group or zero-witness retirements as genuine progress. This
section flags every documented vacuity caveat so external readers can
discount appropriately.

| LEDGER row | LEDGER status | KNOWN_ISSUES location | Mechanism | External-reader DO-NOT-conclude |
|---|---|---|---|---|
| NC1-WITNESS | FORMAL_KERNEL (with vacuity caveat) | §1.1 (line 38) | SU(1) is the trivial group {1}; the unconditional witness `ClayYangMillsMassGap 1` is a structural-completeness fact only | Do NOT conclude that the lattice mass gap is established for SU(N), N ≥ 2 |
| CONTINUUM-COORDSCALE | INVALID-AS-CONTINUUM | §1.2 (line 59) | The "continuum mass gap" was reached via coordinated scaling, an architectural trick rather than analysis | Do NOT count this row as progress toward OUT-CONTINUUM |
| EXP-SUN-GEN | FORMAL_KERNEL (vacuous zero-skew-Hermitian-trace-zero generator family) | §1.3 (line 95) | The "retired" axiom is satisfied by the zero matrix family, not by Pauli / Gell-Mann / standard generators | Do NOT count this retirement as evidence for SU(N) Lie-algebra structure |
| SU(1) OS-style structural axioms (OS0–OS4, cluster, infinite-volume) | structurally honest, physically vacuous | §9 / Finding 011 | Closed only for the abelian SU(1) trivial-group case | Do NOT extrapolate to non-abelian SU(N), N ≥ 2 |
| Branch III analytic predicates (LSI, Poincaré, clustering, Dirichlet form, Markov-semigroup, Feynman-Kac) | structurally honest | §9 / Finding 012 | Same SU(1)-trivial caveat extends through these analytic predicates | Same |
| Bałaban predicate carriers (BalabanHyps, WilsonPolymerActivityBound, LargeFieldActivityBound, SmallFieldActivityBound) | structurally trivially inhabitable | §9 / Findings 013–014 | Inhabited via zero/identity/vacuous witnesses for every N_c ≥ 1 | Do NOT count these as analytic progress on Bałaban RG |
| Codex BalabanRG/ scaffold (~222 files, 0 sorries, 0 axioms) | scaffold | §9 / Finding 015 | Entire Branch II chain to ClayYangMillsTheorem populated with trivial-witness placeholders at every layer | Do NOT count this as Bałaban RG content; treat as bookkeeping |
| Triple-view characterisation (L42 + L43 + L44) | structurally complete, substantively empty | §10.3 (line 427) | Inputs c_Y, c_σ, ω ≠ 1 are anchor structures, NOT derived from first principles | Do NOT count the triple-view as derived; it is structural plumbing |

A reader who counts the vacuity caveats appropriately should expect the
honesty-discounted lattice number (~23–25 %) rather than the headline
~28 %. The Clay-as-stated number (~5 %) does not change because the
discounts apply to lattice-side rows; the Clay-side OUT-* rows have
contribution ~0 % already.

---

## Honesty discipline

- This document is a **plan / honesty instrument**, not a proof. Filing
  it does not move any LEDGER row.
- No `OUT-*` row claims any progress. The three rows remain `BLOCKED` per
  `UNCONDITIONALITY_LEDGER.md` lines 78–80.
- The "% toward Clay-as-stated" estimate (~5 %) is given with the
  obligatory disclaimer that Clay requires the continuum theory the
  project does not currently address.
- The "% toward lattice mass gap" estimate (~28 %, honesty-discounted to
  ~23–25 %) is given with the discount caveat surfacing the vacuous
  FORMAL_KERNEL rows.
- Any future agent updating this document MUST run a Cowork audit first
  if they want to move any percentage; per
  `JOINT_AGENT_PLANNER.md:59–64` percentage changes require LEDGER + bus +
  recommendation entry + README sync.

## Cross-references

- `UNCONDITIONALITY_LEDGER.md` — authoritative dependency map, especially
  Tier 3 lines 74–80 and §38 interim `vacuity_flag` schema (lines 38–75).
- `JOINT_AGENT_PLANNER.md` — the 4-number consensus surface; its
  `forbidden_conclusions` list complements this document.
- `registry/progress_metrics.yaml` — machine-readable percentages
  (audited 17:00Z by `COWORK-AUDIT-JOINT-PLANNER-001`; INFRA_AUDITED
  per `CODEX-PLANNER-LEDGER-MATURE-001` at 10:45Z + Cowork
  `COWORK-AUDIT-CODEX-PLANNER-MATURE-001` at 18:15Z).
- `KNOWN_ISSUES.md` — vacuity caveats (§1.1, §1.2, §1.3, §9 Findings
  011–015, §10.3).
- `MATHEMATICAL_REVIEWERS_COMPANION.md` §3.3 — reviewer-facing
  explanation of `FORMAL_KERNEL` rows with vacuity caveats; complements
  this document.
- `F3_COUNT_DEPENDENCY_MAP.md` — the forward-looking blueprint for
  closing F3-COUNT inside the lattice 28 % column. v1 + v2.53 refresh
  + Codex addenda for v2.55 / v2.56 / v2.57. **Even when F3-COUNT
  closes, the Clay-as-stated number does not move beyond ~10–12 %
  without the OUT-* rows.**
- `F3_MAYER_DEPENDENCY_MAP.md` (filed 19:00Z) — the parallel blueprint for
  F3-MAYER (Brydges-Kennedy random-walk cluster expansion). F3-MAYER is
  BLOCKED until F3-COUNT closes; once it does, the Mayer side is the next
  ~760 LOC of project work (per §(b) difficulty estimates).
- `dashboard/exp_liederivreg_reformulation_options.md` (filed 19:30Z) —
  Cowork's recommended Option 1 (eliminate `lieDerivReg_all` axiom; pass
  `LieDerivReg' f` as explicit hypothesis). When Codex implements Option
  1, Tier 2 axiom count drops 5 → 4 (the only mathematically substantive
  Tier 2 retirement available; unlike the vacuous EXP-SUN-GEN retirement).
- `dashboard/vacuity_flag_column_draft.md` (filed 18:25Z) — concrete
  spec for the LEDGER Tier 1 + Tier 2 `vacuity_flag` column (7 enumerated
  values; per-row recommendations); awaiting Codex implementation.
- `dashboard/mayer_mathlib_precheck.md` (filed 20:20Z) — Mathlib has-vs-
  lacks scope for F3-MAYER §(b)/B.3 (BK forest formula); finding: Mathlib
  lacks the entire Brydges-Kennedy / Mayer / forest-formula stack.

## When to update

Refresh this document when any of:
- An OUT-* row moves off `BLOCKED` (would require Cowork audit and
  LEDGER co-update before the percentage table can change).
- A new vacuity caveat is added to `KNOWN_ISSUES.md`.
- The 4-number consensus in `JOINT_AGENT_PLANNER.md` changes (would
  require Cowork audit per the planner's update protocol).
- F3-COUNT row moves to `FORMAL_KERNEL` (would trigger a `lattice_small_beta`
  bump from 28% → ~43% per `F3_COUNT_DEPENDENCY_MAP.md` §(e); Cowork audit
  required; **Clay-as-stated capped at ~10–12% honest growth ceiling
  remains**).
- F3-MAYER row moves to `FORMAL_KERNEL` (additional ~20% lattice headline
  contribution; same ~10–12% Clay ceiling).
- Codex implements EXP-LIEDERIVREG Option 1 (Tier 2 axiom count 5 → 4;
  honesty-discounted lattice nudges up by ~0–1%; no math row promotion).
- Periodic refresh as cumulative new-context warrants (e.g. this 20:35Z
  refresh after v2.53 → v2.57 progression + 6 deliverables + 6 resolved
  recommendations).

---

*End of Clay-horizon companion. Filed by Cowork as deliverable for
`COWORK-CLAY-HORIZON-AUDIT-001` per dispatcher instruction at
2026-04-26T17:25:00Z. Reviewer-publishable.*
