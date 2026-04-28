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

Current known applications are now recorded directly in the Tier 1 and Tier 2
`vacuity_flag` columns below. The column was delivered on 2026-04-26 from
`dashboard/vacuity_flag_column_draft.md`; keep the enum definitions here as
the authoritative schema reference. Broader vacuity-pattern instances that are
not yet first-class LEDGER rows are consolidated in `KNOWN_ISSUES.md` §1.4 and
explained for reviewers in `MATHEMATICAL_REVIEWERS_COMPANION.md` §3.3.

## Ledger

### Tier 0 — Programme-level

| ID | Claim | Status | Dependency | Evidence | Next action |
|---|---|---|---|---|---|
| CLAY-GOAL | Full Clay-level Yang-Mills existence and mass gap (continuum, SU(N>=2)) | BLOCKED | Complete formal chain through OS reconstruction | FORMALIZATION_ROADMAP_CLAY.md M0-M6 | Close conditional bridges in lower tiers first |
| AGENTIC-INFRA | Codex/Cowork coordination system | INFRA_AUDITED | COWORK-AUDIT-001 audit-pass 2026-04-26T07:30:00Z | AGENT_BUS.md, registry/agent_tasks.yaml | maintenance only |
| AUTOCONTINUE | 24/7 task dispatch system + repeat guard | INFRA_AUDITED | COWORK-AUDIT-AUTOCONTINUE-001 audit-pass 2026-04-26T07:00:00Z | dashboard/codex_autocontinue_snapshot.py + dashboard/autocontinue_validation.txt | NEGCOORDS recheck pending |
| JOINT-PLANNER | Shared Codex/Cowork/Gemma progress planner and percentage ledger | INFRA_AUDITED | COWORK-AUDIT-JOINT-PLANNER-001 audit-pass + stable 5/28/23-25/50 validation | JOINT_AGENT_PLANNER.md, registry/progress_metrics.yaml, scripts/joint_planner_report.py; `python scripts\joint_planner_report.py validate` passed 2026-04-26 | Infrastructure bookkeeping only; no mathematical metric or Clay-status movement |

### Tier 1 — Lattice mass gap (active formalization scope)

| ID | Claim | Status | Dependency | Evidence | vacuity_flag | Next action |
|---|---|---|---|---|---|---|
| L1-HAAR | Haar + Schur on SU(N) | FORMAL_KERNEL (98%) | Mathlib measure theory | sunHaarProb_* family in ClayCore/Schur*.lean | none | Close last 2% |
| L2.4-SCHUR | Structural Schur scaffolding | FORMAL_KERNEL (100%) | L1-HAAR | sidecar files {3a, 3b, 3c} | none | maintenance only |
| L2.5-FROBENIUS | sum int abs(U_ii)^2 <= N Frobenius bound | FORMAL_KERNEL (100%) | L2.4-SCHUR | sunHaarProb_trace_normSq_integral_le (commit 3a3bc6b) | none | maintenance only |
| L2.6-CHARACTER | int abs(tr U)^2 = 1 character inner product | FORMAL_KERNEL (100%) | L2.5-FROBENIUS | sunHaarProb_trace_normSq_integral_eq_one (commit f9ec5e9) | none | maintenance only |
| F3-ANCHOR-SHELL | Anchored root shell (nonempty + bounded + injective code) | FORMAL_KERNEL | L1-HAAR | LatticeAnimalCount.lean v2.42-v2.44 | none | superseded by F3-COUNT |
| F3-COUNT | Klarner BFS-tree lattice-animal count: count(n) <= C * K^n for d=4 | CONDITIONAL_BRIDGE | Full anchored word decoder still incomplete; B.1 safe deletion is closed by v2.63, v2.64 packages the exact physical one-step residual handoff, v2.65 names the finite-alphabet reconstructive deleted-vertex contract, v2.66 records that the contract does not close without a residual parent/frontier invariant, v2.67 lands the invariant interface plus bridge to the contract, v2.68 proves only the local residual-neighbor-parent lemma while leaving residual-only canonicity open, v2.69 factors the exact canonical selector obligation plus bridges it to the invariant/decoder contract, v2.70 isolates the remaining extension-compatibility blocker for any residual-only selector, v2.71 formalizes `PhysicalPlaquetteGraphResidualExtensionCompatibility1296` plus its bridge to the canonical selector, and v2.72 proves the reverse bridge/equivalence while leaving the selector/compatibility theorem open | LatticeAnimalCount.lean v2.48.0 parent selector, v2.50.0 first-deletion/residual primitive, v2.51.0 conditional recursive-deletion handoff (commit `d76b672`), v2.52.0 degree-one leaf deletion subcase (commit `343bfd8`), v2.53.0 safe-deletion hypothesis/driver, v2.54.0 unrooted non-cut deletion, v2.55.0 card-two safe deletion (implementation commit `2ea7a2a`), v2.56.0 bridge (commit `3a90ebc`), v2.57.0 bridge (commit `0d2ebc9`), v2.58.0 card-three safe deletion (commit `2233f40`), v2.59.0 base-zone packaging (commit `e17f316`), v2.60.0 high-cardinality bridge (commit `526a3d4`), v2.61.0 simple-graph bridge (commit `341fcef`), v2.63.0 safe-deletion closure, v2.64.0 `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_erase_mem` plus `physicalPlaquetteGraphAnimalAnchoredWordDecoderBound1296_of_nontrivial`, v2.65.0 `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296` plus `physicalPlaquetteGraphDeletedVertexDecoderStep1296_exists_recoverable_deletion`, v2.66.0 no-closure note `dashboard/f3_reconstructive_contract_attempt_v2_66.md`, v2.67.0 `PhysicalPlaquetteGraphResidualParentInvariant1296` plus `physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_residualParentInvariant1296` with note `dashboard/f3_residual_parent_invariant_v2_67.md`, v2.68.0 `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent` with note `dashboard/f3_residual_parent_invariant_attempt_v2_68.md`, v2.69.0 `PhysicalPlaquetteGraphCanonicalResidualParentSelector1296` plus `physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_canonicalResidualParentSelector1296` with note `dashboard/f3_canonical_residual_parent_selector_v2_69.md`, v2.70.0 no-closure note `dashboard/f3_canonical_selector_attempt_v2_70.md`, and v2.71.0 `PhysicalPlaquetteGraphResidualExtensionCompatibility1296` plus `physicalPlaquetteGraphCanonicalResidualParentSelector1296_of_residualExtensionCompatibility1296` with note `dashboard/f3_residual_extension_compatibility_v2_71.md`, and v2.72.0 `physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296` with note `dashboard/f3_residual_extension_compatibility_attempt_v2_72.md`, v2.73.0 symbolic parent selector interface plus product-symbol bridge, v2.74.0 parent-menu cover isolated as the next symbolic-selector blocker, v2.75.0 residual parent-menu cover interface plus bridge, v2.76.0 cover attempt reduced to frontier-menu bound, v2.77.0 residual-frontier parent-menu bound proposition scoped, v2.78.0 conditional Bound→Covers bridge landed, v2.79.0 bounded search documented raw frontier growth without proof claim, v2.80.0 essential safe-deletion frontier lemma scoped, v2.81.0 essential frontier interface plus bridge landed, v2.82.0 essential frontier proof attempt isolated bounded-indegree orientation, v2.83.0 bounded-indegree orientation/code-bound interface selected, v2.84.0 safe-deletion orientation-code interface plus injection bridge landed, v2.85.0 orientation-code proof attempt isolated canonical policy blocker, v2.86.0 portal-supported orientation policy scoped, v2.87.0 portal-supported orientation interface plus bridge landed, v2.88.0 portal-supported proof attempt isolated root-shell safe-deletion blocker, v2.89.0 root-shell safe-deletion scope recorded root-only portal policy blocker, v2.90.0 flexible multi-portal policy scoped, v2.91.0 multi-portal interface added and triple-symbol arity blocker isolated, v2.92.0 triple-symbol decoder interface plus bridge landed, v2.93.0 multi-portal orientation attempt isolated base-case self-neighbor blocker, v2.94.0 pointed/base-aware multi-portal successor scoped, v2.95.0 `PhysicalPlaquetteGraphBaseAwareMultiPortalProducer1296` interface plus base-aware triple-symbol bridge landed, v2.96.0 base-aware producer attempt stopped at the non-singleton portal-menu bound, v2.97-v2.99 base-aware residual portal-menu scope/interface/attempt isolated the last-step portal image blocker, v2.100-v2.102 base-aware last-step portal image scope/interface/no-closure, v2.103-v2.105 base-aware canonical last-step predecessor scope/interface/last-edge-selector blocker, v2.106-v2.109 canonical last-edge predecessor selector/interface/selected-image blocker plus growth search, v2.110-v2.112 residual last-edge dominating-set scope/interface/no-closure, v2.113-v2.121 terminal-predecessor domination and base-aware bookkeeping interfaces through low-cardinality totalization and base-aware bookkeeping proofs, v2.123-v2.130 dominated/residual-fiber terminal-predecessor packing, domination, and image-bound scopes/interfaces/no-closures, v2.131-v2.137 canonical last-edge image and residual terminal-edge selector scopes/interfaces/producers, v2.138-v2.143 walk terminal-edge and canonical terminal-suffix selected-image scopes/interfaces/blockers, v2.144-v2.149 canonical terminal-neighbor and terminal-neighbor selector-image scopes/interfaces/blockers, v2.150-v2.152 terminal-neighbor image-compression scope/interface/producer blocker, v2.153-v2.155 terminal-neighbor dominating-menu scope/interface/proof blocker, v2.156-v2.158 terminal-neighbor code-separation scope/interface/proof blocker, v2.159-v2.160 terminal-neighbor selector-code separation scope plus interface/bridge landing, v2.161 selector-code separation reduced to the independent selector-image bound blocker, v2.162 non-circular selector-image route scoped, v2.163 geometric selector-code interface/bridge landed, v2.164 geometric selector-code proof attempt isolated basepoint-independent selected-value separation, v2.165 basepoint-independent terminal-neighbor code scoped, and v2.166 `PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296` interface plus `physicalPlaquetteGraphResidualFiberTerminalNeighborGeometricSelectorCode1296_of_residualFiberTerminalNeighborBasepointIndependentCode1296` bridge landed, v2.167 no-closure attempt `dashboard/f3_terminal_neighbor_basepoint_independent_code_attempt_v2_167.md` isolated the missing residual-local absolute selected terminal-neighbor value-code, v2.168 scoped `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296` and its bridge to `PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296` in `dashboard/f3_terminal_neighbor_absolute_selected_value_code_scope.md`, v2.169 missing absolute selected-value interface proof stop `dashboard/f3_terminal_neighbor_absolute_selected_value_code_attempt_v2_169.md` recorded that the absolute selected-value interface/bridge was still missing before any proof could close, and v2.170 `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296` plus `physicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296_of_residualFiberTerminalNeighborAbsoluteSelectedValueCode1296` landed the absolute selected-value interface/bridge in `dashboard/f3_terminal_neighbor_absolute_selected_value_code_interface_v2_170.md`, v2.171-v2.182 advanced the ambient/bookkeeping-tag/tag-map/selector-source chain via `dashboard/f3_terminal_neighbor_absolute_selected_value_code_attempt_v2_171.md`, `dashboard/f3_terminal_neighbor_ambient_value_code_scope.md`, `dashboard/f3_terminal_neighbor_ambient_value_code_interface_v2_173.md`, `dashboard/f3_terminal_neighbor_ambient_value_code_attempt_v2_174.md`, `dashboard/f3_terminal_neighbor_ambient_bookkeeping_tag_code_scope.md`, `dashboard/f3_terminal_neighbor_ambient_bookkeeping_tag_code_interface_v2_176.md`, `dashboard/f3_terminal_neighbor_ambient_bookkeeping_tag_code_attempt_v2_177.md`, `dashboard/f3_residual_fiber_bookkeeping_tag_map_scope.md`, `dashboard/f3_residual_fiber_bookkeeping_tag_map_interface_v2_179.md`, `dashboard/f3_residual_fiber_bookkeeping_tag_map_attempt_v2_180.md`, `dashboard/f3_residual_fiber_terminal_neighbor_selector_source_scope.md`, and v2.182 `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296` plus `PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296` with two-premise bridge `physicalPlaquetteGraphResidualFiberBookkeepingTagMap1296_of_residualFiberTerminalNeighborSelectorSource1296_of_residualFiberBookkeepingTagCodeForSelector1296` in `dashboard/f3_residual_fiber_terminal_neighbor_selector_source_interface_v2_182.md`, v2.183-v2.216 are now reconciled as a documentation-only endpoint by `dashboard/axiom_frontier_f3_v2_188_v2_216_reconcile.md` and scoped in `dashboard/ledger_f3_count_evidence_column_extend_v2_183_v2_216_scope.md`: v2.183-v2.187 reconcile the selector-source/domination/selector-data-source proof-stop chain; v2.188-v2.195 close the non-singleton walk-split to selector-source path; v2.196-v2.214 advance the bookkeeping-tag/base-zone interface/no-closure chain to the missing `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`; and v2.216 records retrospective non-circular research/audit only, with no proof-status movement | caveat-only | Prove the residual-only selector/compatibility obligation (`PhysicalPlaquetteGraphCanonicalResidualParentSelector1296`, equivalently `PhysicalPlaquetteGraphResidualExtensionCompatibility1296`); then instantiate `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`, build the full anchored word decoder, and audit before any F3-COUNT status or percentage move |
| F3-MAYER | Brydges-Kennedy random-walk cluster expansion: abs(K(Y)) <= A0 * r^abs(Y) | BLOCKED | F3-COUNT closure preferred first | BLUEPRINT_F3Mayer.md | none | ~700 LOC across 4 files when F3-COUNT lands |
| F3-COMBINED | clayMassGap_smallBeta_for_N_c for N_c >= 2 at beta < 1/(28 N_c) | BLOCKED | F3-COUNT and F3-MAYER both | clayMassGap_of_shiftedF3MayerCountPackageExp skeleton landed | none | Mechanical glue once F3-COUNT and F3-MAYER close |
| NC1-WITNESS | ClayYangMillsMassGap 1 unconditional | FORMAL_KERNEL (with caveat) | AbelianU1Unconditional.lean | oracle-clean | trivial-group | Vacuous: SU(1) = {1}, connected correlator = 0; rename file (per FINAL_HANDOFF.md desk decision §1) |
| CONTINUUM-COORDSCALE | HasContinuumMassGap via coordinated scaling | INVALID-AS-CONTINUUM | architectural trick, not analysis | KNOWN_ISSUES.md §1.2, Finding 004 | trivial-placeholder | Refactor (Option C of GENUINE_CONTINUUM_DESIGN.md), pending Lluis decision |

### Tier 2 — Experimental axioms (4 real active declarations in `Experimental/`; archived spike excluded)

| ID | Claim | Status | Retire effort | vacuity_flag | Next action |
|---|---|---|---|---|---|
| EXP-SUN-GEN | SU(N) generator data for the experimental Lie-derivative stack | FORMAL_KERNEL (vacuous) | Retired in current API by zero skew-Hermitian trace-zero matrix family | zero-family | `LieDerivativeRegularity.lean` now defines `generatorMatrix` and proves `gen_skewHerm` / `gen_trace_zero`; build `lake build YangMills.Experimental.LieSUN.LieDerivativeRegularity` passed; this is **not** a basis construction, see `KNOWN_ISSUES.md` §1.3 |
| EXP-MATEXP-DET | matExp_traceless_det_one | EXPERIMENTAL | Medium (~50 LOC + Mathlib PR) | none | Mirror MatrixExp_DetTrace_DimOne_PR.lean |
| EXP-LIEDERIVREG | lieDerivReg_all | INVALID | Mathematically false as stated; needs reformulation | caveat-only | Restrict to smooth f |
| EXP-BAKRYEMERY-SPIKE | sun_haar_satisfies_lsi | ARCHIVED-SPIKE | Archived; the alleged axiom was comment-only in an unimported spike file, not an active Lean declaration | caveat-only | `YangMills/Experimental/_archive/BakryEmerySpike.lean` preserved with `[SPIKE - ARCHIVED]` banner; no mathematical status upgraded |
| EXP-BD-HY-GR | variance-decay / Gronwall semigroup axioms (2 real declarations) | EXPERIMENTAL | Hard (Mathlib infrastructure) | caveat-only | Long-tail; await Mathlib upstream |

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

