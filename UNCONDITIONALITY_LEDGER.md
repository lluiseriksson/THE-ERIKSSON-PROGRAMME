# UNCONDITIONALITY_LEDGER.md

This ledger tracks every assumption, bridge, axiom, placeholder, conditional
theorem, experimental result, and unresolved blocker on the path to a fully
unconditional Clay-level Yang-Mills mass gap formalization.

It is the **authoritative dependency map** of the project. Every claim about
"what is proved" or "what remains" must be reconcilable with this file.

## Global Clay status

Status:
- NOT_ESTABLISHED

Reason:
- The repository does not yet contain a complete unconditional formal proof of
  the Clay Yang-Mills Mass Gap problem.

Honesty rule (per AGENTS.md §8):
- No agent may upgrade this status to ESTABLISHED unless the repository contains
  (a) a complete formal Lean proof chain whose `#print axioms` reduces to
  `[propext, Classical.choice, Quot.sound]` only, (b) an audit-pass entry in
  `registry/agent_history.jsonl`, (c) a row in this ledger pointing to the
  exact theorem name and commit SHA, and (d) sign-off in
  `COWORK_RECOMMENDATIONS.md`.

## Status labels

- FORMAL_KERNEL: verified by Lean without project-specific assumptions
- MATHLIB_FOUNDATIONAL: depends only on accepted Lean/Mathlib foundations
- CONDITIONAL_BRIDGE: depends on an explicitly stated unproved mathematical bridge
- INFRA_AUDITED: meta-infrastructure verified by Cowork audit (NOT a math claim)
- EXPERIMENTAL: exploratory and not part of the proof chain
- HEURISTIC: motivational or strategic only
- BLOCKED: cannot progress without a theorem, definition, or decision
- INVALID: must not be used

## Vacuity flags (interim schema)

`vacuity_flag` is an honesty annotation, not a proof status.  It records
whether a formally verified row is mathematically low-content, degenerate, or
only a structural carrier.  It must never upgrade a row and must never be used
to imply progress for physical `SU(N)` Yang-Mills with `N >= 2`.

Intended values:

- none: no known vacuity caveat.
- caveat-only: genuine formal content exists, but reviewers must read a caveat
  before interpreting the row externally.
- vacuous-witness: the formal witness exists because the target proposition is
  weak, empty, or trivially inhabitable.
- trivial-group: the witness uses `SU(1)` or another degenerate group case and
  does not transfer to `SU(N)` for `N >= 2`.
- zero-family: the witness uses the zero object/family to satisfy shape
  predicates, without supplying the intended nonzero spanning/basis data.
- anchor-structure: the row proves scaffolding or carrier shape, not the
  analytic content that external readers may expect.
- trivial-placeholder: the row is a placeholder or bookkeeping endpoint whose
  inhabitant should not be described as mathematical progress.

Current known applications before the full column migration:

| Row | Intended vacuity_flag | Caveat |
|---|---|---|
| NC1-WITNESS | trivial-group | `ClayYangMillsMassGap 1` is oracle-clean but uses `SU(1) = {1}`; it is not evidence for `N_c >= 2`. |
| EXP-SUN-GEN | zero-family | The retired generator data uses `generatorMatrix := 0`; it is not a Pauli/Gell-Mann/general `su(N)` generator basis. |
| CONTINUUM-COORDSCALE | trivial-placeholder | Marked `INVALID-AS-CONTINUUM`; it must not be counted as continuum-limit progress. |
| Balaban / OS-style structural carriers mentioned in `KNOWN_ISSUES.md` §9 | anchor-structure | Carrier inhabitation does not supply the analytic Wilson/Gibbs/Balaban content. |
| Clay weak endpoint canaries | vacuous-witness | `ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys` is trivially inhabited. |

Implementation note (2026-04-26): the full Tier 1 + Tier 2 table column is
blocked on `dashboard/vacuity_flag_column_draft.md`, which has not yet been
delivered.  Until that draft exists, this schema is the authoritative interim
reader guidance.  The companion reviewer explanation lives in
`MATHEMATICAL_REVIEWERS_COMPANION.md`.

## Ledger

### Tier 0 — Programme-level

| ID | Claim | Status | Dependency | Evidence | Next action |
|---|---|---|---|---|---|
| CLAY-GOAL | Full Clay-level Yang-Mills existence and mass gap (continuum, SU(N>=2)) | BLOCKED | Complete formal chain through OS reconstruction | FORMALIZATION_ROADMAP_CLAY.md M0-M6 | Close conditional bridges in lower tiers first |
| AGENTIC-INFRA | Codex/Cowork coordination system | INFRA_AUDITED | COWORK-AUDIT-001 audit-pass 2026-04-26T07:30:00Z | AGENT_BUS.md, registry/agent_tasks.yaml | maintenance only |
| AUTOCONTINUE | 24/7 task dispatch system + repeat guard | INFRA_AUDITED | COWORK-AUDIT-AUTOCONTINUE-001 audit-pass 2026-04-26T07:00:00Z | dashboard/codex_autocontinue_snapshot.py + dashboard/autocontinue_validation.txt | NEGCOORDS recheck pending |
| JOINT-PLANNER | Shared Codex/Cowork/Gemma progress planner and percentage ledger | INFRA_AUDITED | COWORK-AUDIT-JOINT-PLANNER-001 audit-pass + stable 5/28/23-25/50 validation | JOINT_AGENT_PLANNER.md, registry/progress_metrics.yaml, scripts/joint_planner_report.py; `python scripts\joint_planner_report.py validate` passed 2026-04-26 | Infrastructure bookkeeping only; no mathematical metric or Clay-status movement |

### Tier 1 — Lattice mass gap (active formalization scope)

| ID | Claim | Status | Dependency | Evidence | Next action |
|---|---|---|---|---|---|
| L1-HAAR | Haar + Schur on SU(N) | FORMAL_KERNEL (98%) | Mathlib measure theory | sunHaarProb_* family in ClayCore/Schur*.lean | Close last 2% |
| L2.4-SCHUR | Structural Schur scaffolding | FORMAL_KERNEL (100%) | L1-HAAR | sidecar files {3a, 3b, 3c} | maintenance only |
| L2.5-FROBENIUS | sum int abs(U_ii)^2 <= N Frobenius bound | FORMAL_KERNEL (100%) | L2.4-SCHUR | sunHaarProb_trace_normSq_integral_le (commit 3a3bc6b) | maintenance only |
| L2.6-CHARACTER | int abs(tr U)^2 = 1 character inner product | FORMAL_KERNEL (100%) | L2.5-FROBENIUS | sunHaarProb_trace_normSq_integral_eq_one (commit f9ec5e9) | maintenance only |
| F3-ANCHOR-SHELL | Anchored root shell (nonempty + bounded + injective code) | FORMAL_KERNEL | L1-HAAR | LatticeAnimalCount.lean v2.42-v2.44 | superseded by F3-COUNT |
| F3-COUNT | Klarner BFS-tree lattice-animal count: count(n) <= C * K^n for d=4 | CONDITIONAL_BRIDGE | Recursive deletion / full word decoder still incomplete; v2.54 proves the Mathlib-backed unrooted non-cut deletion step, v2.55 proves the root-avoiding safe-deletion base case for `k = 2`, v2.56 proves safe deletion is equivalent to the exact non-root non-cut formulation, v2.57 proves a global two-non-cut theorem would imply the non-root non-cut/safe-deletion gap, and v2.58 proves the root-avoiding safe-deletion base case for `k = 3`; the global two-non-cut or non-root non-cut theorem remains open | LatticeAnimalCount.lean v2.48.0 parent selector, v2.50.0 first-deletion/residual primitive, v2.51.0 conditional recursive-deletion handoff (commit `d76b672`), v2.52.0 degree-one leaf deletion subcase (commit `343bfd8`), v2.53.0 safe-deletion hypothesis/driver, v2.54.0 unrooted non-cut deletion, v2.55.0 card-two safe deletion (implementation commit `2ea7a2a`), v2.56.0 bridge (commit `3a90ebc`), v2.57.0 bridge (commit `0d2ebc9`), and v2.58.0 card-three safe deletion (commit `<TBD-after-commit>`): `plaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem_of_card_three`, physical specialization | Continue `CLAY-F3-COUNT-RECURSIVE-001`: prove `PlaquetteGraphAnchoredTwoNonCutExists` globally (or prove `PlaquetteGraphAnchoredNonRootNonCutExists` directly), derive `PlaquetteGraphAnchoredSafeDeletionExists` via v2.56/v2.57, then iterate into the full anchored word decoder |
| F3-MAYER | Brydges-Kennedy random-walk cluster expansion: abs(K(Y)) <= A0 * r^abs(Y) | BLOCKED | F3-COUNT closure preferred first | BLUEPRINT_F3Mayer.md | ~700 LOC across 4 files when F3-COUNT lands |
| F3-COMBINED | clayMassGap_smallBeta_for_N_c for N_c >= 2 at beta < 1/(28 N_c) | BLOCKED | F3-COUNT and F3-MAYER both | clayMassGap_of_shiftedF3MayerCountPackageExp skeleton landed | Mechanical glue once F3-COUNT and F3-MAYER close |
| NC1-WITNESS | ClayYangMillsMassGap 1 unconditional | FORMAL_KERNEL (with caveat) | AbelianU1Unconditional.lean | oracle-clean | Vacuous: SU(1) = {1}, connected correlator = 0; rename file (per FINAL_HANDOFF.md desk decision §1) |
| CONTINUUM-COORDSCALE | HasContinuumMassGap via coordinated scaling | INVALID-AS-CONTINUUM | architectural trick, not analysis | KNOWN_ISSUES.md §1.2, Finding 004 | Refactor (Option C of GENUINE_CONTINUUM_DESIGN.md), pending Lluis decision |

### Tier 2 — Experimental axioms (5 real declarations in `Experimental/`)

| ID | Claim | Status | Retire effort | Next action |
|---|---|---|---|---|
| EXP-SUN-GEN | SU(N) generator data for the experimental Lie-derivative stack | FORMAL_KERNEL (vacuous) | Retired in current API by zero skew-Hermitian trace-zero matrix family | `LieDerivativeRegularity.lean` now defines `generatorMatrix` and proves `gen_skewHerm` / `gen_trace_zero`; build `lake build YangMills.Experimental.LieSUN.LieDerivativeRegularity` passed; this is **not** a basis construction, see `KNOWN_ISSUES.md` §1.3 |
| EXP-MATEXP-DET | matExp_traceless_det_one | EXPERIMENTAL | Medium (~50 LOC + Mathlib PR) | Mirror MatrixExp_DetTrace_DimOne_PR.lean |
| EXP-LIEDERIVREG | lieDerivReg_all | INVALID | Mathematically false as stated; needs reformulation | Restrict to smooth f |
| EXP-BAKRYEMERY-SPIKE | sun_haar_satisfies_lsi | EXPERIMENTAL | Classification pending: live spike vs archive | CODEX-LEDGER-EXPERIMENTAL-COUNT-AMEND-001 / Cowork recommendation REC-COWORK-BAKRYEMERY-SPIKE-CLASSIFY-001 |
| EXP-BD-HY-GR | variance-decay / Gronwall semigroup axioms (2 real declarations) | EXPERIMENTAL | Hard (Mathlib infrastructure) | Long-tail; await Mathlib upstream |

### Tier 3 — Outside-current-scope items

| ID | Claim | Status | Reason | Resolution path |
|---|---|---|---|---|
| OUT-CONTINUUM | Continuum limit `a -> 0` via Balaban RG to convergence | BLOCKED | Massive separate research project | 5+ year horizon |
| OUT-OS-WIGHTMAN | Osterwalder-Schrader / Wightman reconstruction | BLOCKED | Required by literal Clay statement | Field-theoretic Mathlib infrastructure missing |
| OUT-STRONG-COUPLING | Mass gap at beta > beta_c (strong coupling) | BLOCKED | Cluster expansion diverges | Different techniques needed |

## Pending audits

- The Codex sync of 2026-04-26 (commit `dfbcf7f`) imported ~340 Lean files. `lake build YangMills` (full graph) timed out at 15 min locally. **Master import graph is integration-pending until a long CI run records a green full build.**
- The 17-20 Mathlib PR-ready files in `mathlib_pr_drafts/` have **not been built with `lake build`** against current Mathlib master. CLAY-MATHLIB-PR-LANDING-001 (READY priority 7) opens this pipeline.
- NEGCOORDS bugfix in `dashboard/codex_autocontinue_snapshot.py` — pending Cowork recheck per audit_state.

## Update protocol

This file is updated by:
1. Cowork when an audit changes the status of any claim (axiom retired, bridge proved, blocker resolved, new conditional bridge discovered).
2. Codex when implementation lands a formal artifact that affects a ledger entry (oracle confirmation required: `#print axioms` returning `[propext, Classical.choice, Quot.sound]` only).
3. Both at session bookend, to reconcile against `STATE_OF_THE_PROJECT.md`.

Every status change must reference: (a) the commit SHA, (b) the theorem name or audit document, (c) the date.
