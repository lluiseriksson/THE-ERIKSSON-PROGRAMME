# KNOWN_ISSUES.md

**Author**: Cowork agent (Claude), public-facing summary 2026-04-25
**Audience**: external readers, mathematicians, physicists, formal-
verification practitioners evaluating THE-ERIKSSON-PROGRAMME
**Purpose**: single-page consolidated summary of all known caveats,
limitations, and open questions, eliminating the need to read 5+
separate strategic documents

For the **detailed** discussion of each item, see the linked
documents. This file is a **synthesis**, not a substitute.

---

## 0. The most important caveat (read this first)

**This formalisation does NOT claim to solve the Clay Yang–Mills
Millennium Prize problem.**

It targets the **lattice mass gap** of SU(N_c) Wilson Yang–Mills at
small inverse coupling β, which is one input toward — but not
identical with — the Clay statement. The continuum limit (`a → 0`,
Wightman / Osterwalder–Schrader axioms, dimensional transmutation)
is structurally outside the project's current scope.

When the project closes its current critical path (the F3 frontier),
the result will be a fully checked machine proof of a non-trivial
theorem of mathematical physics, but **not** the Clay Millennium
theorem.

For the precise distinction, see `MID_TERM_STATUS_REPORT.md` §6.3
"What the Clay Millennium statement requires beyond this".

---

## 1. Witness caveats

### 1.1 The N_c = 1 unconditional witness is technically valid but physically degenerate

**File**: `YangMills/ClayCore/AbelianU1Unconditional.lean`
**Theorem**: `u1_clay_yangMills_mass_gap_unconditional :
ClayYangMillsMassGap 1`
**Issue**: `Matrix.specialUnitaryGroup (Fin 1) ℂ = {1}` is the
**trivial group** (singleton), NOT the abelian QED-like U(1) gauge
theory (which would use `unitaryGroup (Fin 1)`, the unit circle).
The Wilson connected correlator vanishes identically on the
trivial group, so the bound `|0| ≤ C · exp(-m · dist)` is satisfied
trivially.

The Lean construction is sound. The physics content is degenerate.
**This is not the QED-like abelian case**; it is the case where
there is no gauge dynamics at all.

**The first physically non-trivial Clay-grade witness still
requires `N_c ≥ 2`**, which is exactly the F3 frontier target.

**Reference**: `COWORK_FINDINGS.md` Finding 003.

### 1.2 `ClayYangMillsPhysicalStrong` reached via coordinated scaling, not genuine continuum analysis

**Files**:
- `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean` (the v1.84.0
  endpoints)
- `YangMills/L7_Continuum/ContinuumLimit.lean` (the
  `HasContinuumMassGap` definition)

**Issue**: `ClayYangMillsPhysicalStrong` is the conjunction of two
fields:

- `IsYangMillsMassProfile m_lat` — the mass profile actually bounds
  Wilson correlators. **Genuine** when supplied by the F3 chain.
- `HasContinuumMassGap m_lat` — the renormalised mass converges to
  a positive limit. **Satisfied via an architectural coordination
  of the repository**:

  ```
  latticeSpacing N := 1/(N+1)
  constantMassProfile m N := m/(N+1)        -- not constant in N
  renormalizedMass = (m/(N+1)) / (1/(N+1)) = m  -- trivially converges
  ```

**The continuum half is NOT genuine continuum analysis** (Bałaban
RG, Osterwalder–Schrader, dimensional transmutation). It is
satisfied by definition of the coordinated scaling.

**Implication**: when external descriptions say "the project
reaches `ClayYangMillsPhysicalStrong`", they should add the
qualifier "with the continuum half satisfied via the coordinated
scaling convention rather than genuine continuum analysis".

**References**: `COWORK_FINDINGS.md` Finding 004,
`GENUINE_CONTINUUM_DESIGN.md`,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §6.2.

### 1.3 The EXP-SUN-GEN axiom retirement is technically valid but vacuous (zero matrix family, not Gell-Mann/Pauli)

**Files**: `YangMills/Experimental/LieSUN/LieDerivativeRegularity.lean` (lines
24–34), `UNCONDITIONALITY_LEDGER.md` Tier 2 row `EXP-SUN-GEN`,
`EXPERIMENTAL_AXIOMS_AUDIT.md` §1.

**Theorems**:
- `def generatorMatrix (N_c : ℕ) [NeZero N_c] (_i : Fin (N_c ^ 2 - 1)) : Matrix (Fin N_c) (Fin N_c) ℂ := 0`
- `theorem gen_skewHerm := by simp [generatorMatrix]`
- `theorem gen_trace_zero := by simp [generatorMatrix]`

**Issue**: the three former axioms `generatorMatrix`, `gen_skewHerm`,
`gen_trace_zero` were retired by setting the matrix family to **zero** and
proving the skew-Hermitian and trace-zero properties trivially via `simp`.
The retirement is honest at the Lean level (3 axioms → 3 theorems, the
ledger row `EXP-SUN-GEN` correctly upgraded `EXPERIMENTAL → FORMAL_KERNEL`)
but **vacuous** at the math level: the zero matrix is skew-Hermitian and
trace-zero trivially, and a family of zero matrices is **not** the SU(N)
generator basis (Pauli for N=2, Gell-Mann for N=3, or the general standard
basis `{E_{ij} - E_{ji}, i(E_{ij} + E_{ji}), H_k}`).

The Lean code is sound. **The math content is degenerate**: this retirement
does not provide an actual SU(N) Lie-algebra basis.

The docstring is **explicit and honest**: *"This API is only used to provide
a skew-Hermitian, trace-zero matrix family for the experimental
Lie-derivative stack; it does not currently require basis spanning or
linear-independence data. The zero family therefore retires the old data
axiom **without strengthening any downstream claim**."*

**Why it has not exploded**: as of 2026-04-26, the four files that consume
`generatorMatrix` are all inside `YangMills/Experimental/`
(`LieDerivativeRegularity.lean`, `LieDerivReg_v4.lean`,
`GeneratorAxiomsDimOne.lean`, `DirichletConcrete.lean`). None of them
require linear independence or basis-spanning. The Clay chain
(`ClayCore/`) does not touch `generatorMatrix` at all.

**Implication**: when external descriptions say "the project retired the
SU(N) generator-data axioms", they should add the qualifier "via the zero
matrix family, not via Pauli/Gell-Mann generators — a real generator basis
remains future work, tracked as `CODEX-IMPLEMENT-REAL-GENERATORS-001`".

**The first physically non-trivial SU(N) generator data still requires a
real basis**, which is exactly the `CODEX-IMPLEMENT-REAL-GENERATORS-001`
follow-up task target. That task auto-promotes from FUTURE to READY when
any downstream consumer files a recommendation requiring real generators.

**References**: `UNCONDITIONALITY_LEDGER.md` Tier 2 row `EXP-SUN-GEN`,
`EXPERIMENTAL_AXIOMS_AUDIT.md` §1, `COWORK_RECOMMENDATIONS.md`
2026-04-26T11:00:00Z audit entry, `COWORK_FINDINGS.md` Finding 003 (the
analogous NC1-WITNESS vacuity case).

**Same shape as §1.1**: NC1-WITNESS is technically valid (oracle-clean
`ClayYangMillsMassGap 1`) but vacuous (SU(1) trivial group, connected
correlator vanishes identically). EXP-SUN-GEN follows the same pattern at
the Tier 2 level: technically valid (3 axioms → 3 theorems), vacuous (zero
matrix family).

### 1.4 Consolidated vacuity rules for external readers

This section consolidates the vacuity-pattern caveats that were previously
spread across §1.1, §1.2, §1.3, §9, §10.3, and `COWORK_FINDINGS.md`
Findings 003 + 011-016. It is an honesty index, not a new mathematical claim.
No entry below is closed merely by being listed here.

Rule:

```
Lean-verified carrier or witness + vacuity flag = read the caveat before
describing the result externally.
```

| Claim / pattern | Tier or location | Mechanism | Lean witness location | External-reader DO-NOT-conclude template |
|---|---|---|---|---|
| `NC1-WITNESS` | Tier 1 | `SU(1)` is the trivial group; the connected correlator vanishes identically | `YangMills/ClayCore/AbelianU1Unconditional.lean` | Do not conclude a physical `SU(N)` mass gap for `N >= 2`. |
| `EXP-SUN-GEN` | Tier 2 | `generatorMatrix := 0` retires shape axioms but supplies no nonzero generator basis | `YangMills/Experimental/LieSUN/LieDerivativeRegularity.lean` | Do not conclude Pauli/Gell-Mann/general `su(N)` generator data has been constructed. |
| OS-style structural axioms at `SU(1)` | Finding 011 | Structural predicates are inhabitable in the degenerate group case | OS/continuum scaffold files cited in `COWORK_FINDINGS.md` Finding 011 | Do not conclude Wightman/OS reconstruction for nonabelian continuum Yang-Mills. |
| Branch III analytic predicates | Finding 012 | LSI, Poincare, clustering, Dirichlet, Markov-semigroup, and Feynman-Kac predicate carriers inherit the `SU(1)` caveat | Branch III scaffold files cited in Finding 012 | Do not conclude analytic inequalities have been proved for physical Wilson-Gibbs data. |
| Bałaban predicate carriers | Findings 013-014 | `BalabanHyps`, Wilson activity, large-field, and small-field carriers are structurally inhabitable by zero / identity / vacuous witnesses | Bałaban carrier files cited in Findings 013-014 | Do not conclude Bałaban RG convergence or Wilson activity estimates. |
| BalabanRG scaffold to weak endpoint | Finding 015 | A large 0-sorry scaffold reaches a weak endpoint through trivial-witness placeholders | `YangMills/BalabanRG/` and comments in `RGContractionRate.lean` | Do not conclude substantive Branch II Clay closure. |
| `ClayCoreLSI` | Finding 016 | The named predicate is an arithmetic existential, not the integral log-Sobolev inequality | `ClayCoreLSI` / `ClayCoreLSIToSUNDLRTransfer` files cited in Finding 016 | Do not conclude LSI for SU(N) Wilson-Gibbs measures; the transfer theorem remains the substantive target. |
| Triple-view characterisation | §10.3 | L42/L43/L44 input dimensionless constants as anchor structures rather than deriving them | L42/L43/L44 files cited in §10.3 | Do not conclude Wilson area law or confinement from first principles. |
| `CONTINUUM-COORDSCALE` | Tier 1 / Finding 004 | Coordinated scaling makes the continuum field true by architecture, not continuum analysis | `YangMills/L7_Continuum/ContinuumLimit.lean` | Do not count this as a proof of the continuum limit. |
| Clay weak endpoint canaries | Terminal/audit scaffolds | `ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys` is trivially inhabited | `YangMills/L8_Terminal/ClayTrivialityAudit.lean` | Do not cite this as the Clay mass-gap theorem. |

`UNCONDITIONALITY_LEDGER.md` records first-class Tier 1 and Tier 2 rows with a
`vacuity_flag` column. Patterns that are not yet first-class ledger rows remain
tracked here until a separate ledger-row task promotes them.

---

## 2. Axiom and sorry status

### 2.1 The 0-axiom invariant outside `Experimental/`

**Status**: ENFORCED.

`grep -rn "^axiom " --include="*.lean" YangMills/ | grep -v
Experimental` returns empty. Verified by daily auto-audit (HR3 of
`CODEX_CONSTRAINT_CONTRACT.md`).

### 2.2 Live `sorry` count outside `Experimental/`

**Status**: 0.

`SORRY_FRONTIER.md` records `Current sorry count: 0`. Verified by
refined regex check in the daily audit (HR4).

### 2.3 Active axioms inside `YangMills/Experimental/`

**Status**: 4 active real declarations remain after generator-data retirement
and Bakry-Emery spike archival.

| Group | Count | Retire effort |
|---|---:|---|
| `matExp_traceless_det_one` (needs bridge) | 1 | medium (~50 LOC + Mathlib PR) |
| `lieDerivReg_all` (smuggling — false for arbitrary `f`) | 1 | needs reformulation |
| variance-decay + Gronwall semigroup axioms | 2 | hard (Mathlib / C₀-semigroup infrastructure) |

**Reference**: `EXPERIMENTAL_AXIOMS_AUDIT.md`.

The former SU(N) generator-data axioms were retired using the zero-family API
described in §1.3. `YangMills/Experimental/_archive/BakryEmerySpike.lean` is
preserved as historical reconnaissance only; its former `sun_haar_satisfies_lsi`
text was comment-only and is excluded from the active axiom inventory.

**`lieDerivReg_all` is mathematically false** as stated (it asserts
regularity for **every** `f : SU(N) → ℝ`, including discontinuous
ones). Currently scoped to `Experimental/` so does not affect any
non-Experimental theorem, but should be reformulated.

---

## 3. Bibliographic issues

### 3.1 Battle-Federbush 1984 — not pinned

**Where cited**: `BLUEPRINT_F3Mayer.md` §3.1,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §5.2.
**Issue**: cited as "Battle-Federbush 1984 (random walks in cluster
expansions)" without exact title or journal.
**Suggested resolution** (per `REFERENCES_AUDIT.md` §1.4):
`G. Battle, P. Federbush, "A note on cluster expansions, tree graph
identities, extra 1/N! factors!!!", Lett. Math. Phys. 8 (1984), 1-3`.
**Verify before academic publication.**

### 3.2 Hölzl-Immler Peter-Weyl Isabelle reference — uncertain

**Where cited**: `PETER_WEYL_ROADMAP.md` §5,
`PETER_WEYL_ROADMAP_HISTORY.md` (preserved).
**Issue**: cited as "Hölzl & Immler, *Peter-Weyl theorem in
Isabelle/HOL*" without exact paper title. Existence of such a
formalisation is uncertain.
**Suggested resolution**: verify before academic publication; if
no such paper exists, replace with the actual nearest analogue or
remove the citation.

---

## 4. Process / governance status

### 4.1 NEXT_SESSION.md previously contained a polynomial-frontier contradiction

**File**: `YangMills/ClayCore/NEXT_SESSION.md`
**Issue (resolved)**: NEXT_SESSION.md described both the
**polynomial** F3 packages (now infeasible per Finding 001) and the
**exponential** F3 packages (the active route from v1.79.0+) in
parallel, without clear hierarchy. A future Codex session reading
the polynomial subtarget literally could waste days on a target
that cannot close.
**Resolution (2026-04-25 ~10:55 UTC)**: banner added at the top of
NEXT_SESSION.md flagging the exponential route as canonical.
**Reference**: `COWORK_FINDINGS.md` Finding 006.

### 4.2 `L4_LargeField/Suppression.lean` is orphaned

**File**: `YangMills/L4_LargeField/Suppression.lean`
**Issue**: 0 importers (per `LAYER_AUDIT.md`). Contains valid
oracle-clean Lean (~85 LOC) for the large-field suppression
integral; just disconnected from the active F3 frontier.
**Status**: observational. Cowork agent recommends keeping with
an annotation noting it is orphaned and preserved for potential
future Bałaban RG work, but Lluis has not yet decided.
**Reference**: `COWORK_FINDINGS.md` Finding 005.

### 4.3 Dual-governance dead weight

**Files**: `AI_ONBOARDING.md`, `registry/` (8 YAML files),
`dashboard/current_focus.json`, parts of `scripts/`
**Issue**: the repository contains **two parallel governance
systems** (per `REPO_INFRASTRUCTURE_AUDIT.md`). The older system
(March 2026, built around L0-L8 nodes) has been abandoned but
not removed. Most of its files are 3-6 weeks stale (e.g.,
`AI_ONBOARDING.md` cites v1.45.0 vs current v1.89.0;
`dashboard/current_focus.json` is dated 2026-03-12).
**Status**: advisory. Codex doesn't consult these; only new
contributors / AI agents reading the project cold would be
misled. **Reference**: `COWORK_FINDINGS.md` Finding 007 +
`REPO_INFRASTRUCTURE_AUDIT.md`.

---

## 5. Documentation freshness

### 5.1 Strategic doc inconsistencies (mostly resolved)

The Cowork session of 2026-04-25 surfaced and resolved most
strategic-doc inconsistencies:

- `STATE_OF_THE_PROJECT.md`: was at v0.34.0; rewritten to v1.85.0.
- `ROADMAP.md`: refreshed to v1.85.0.
- `UNCONDITIONALITY_ROADMAP.md`: 2026-04-25 update inserted.
- `PETER_WEYL_ROADMAP.md`: trimmed 574→132 lines, content
  preserved in `PETER_WEYL_ROADMAP_HISTORY.md`.
- `NEXT_SESSION.md`: banner added (per §4.1 above).

### 5.2 Remaining mild staleness

- `README.md` §3 milestones: extended to include v1.79–v1.85 work
  (this session); §6 ladder rows added for v1.79–v1.85; §7
  repository layout still missing some new files (low priority).
- `ROADMAP_MASTER.md`: high-level, low-priority refresh deferred.
- `PHASE8_PLAN.md` and `PHASE8_SUMMARY.md`: marked stale via
  banners; not on critical path.

---

## 6. What is open (and what is not)

### Currently open in the active F3 frontier

| Item | Priority | Estimated effort | Reference |
|---|---|---|---|
| Klarner BFS-tree count witness | 1.2 (active) | ~310 LOC remaining | `AUDIT_v185_LATTICEANIMAL.md` |
| Brydges-Kennedy estimate (F3-Mayer side) | 2.x | ~700 LOC across 4 files | `BLUEPRINT_F3Mayer.md` §4.1 |
| Combined F3 packaging witness | 3.x | ~50 LOC glue | follows from 1.2 + 2.x |
| `clayMassGap_smallBeta_for_N_c` for N_c ≥ 2 | 4.x | mechanical | follows from 3.x |

### NOT in scope (and why)

| Item | Why out of scope |
|---|---|
| Continuum limit `a → 0` | Requires Bałaban RG to convergence; massive separate project |
| Wightman / Osterwalder-Schrader axioms | The Clay statement requires them; project is lattice-only |
| Strong-coupling / non-perturbative regime `β > β_c` | Cluster expansion diverges; different techniques needed |
| Clay Millennium statement itself | See §0 and the items above |

### NOT planned but possibly worth doing

- Retire the 7 easy-retire Experimental axioms (see §2.3).
- Reformulate the `lieDerivReg_all` smuggling axiom.
- Pursue Mathlib upstream PRs (drafts exist in `mathlib_pr_drafts/`).
- Refactor `HasContinuumMassGap` to take a spacing scheme parameter
  (Option C of `GENUINE_CONTINUUM_DESIGN.md` — recommended before
  any external Clay announcement).

---

## 7. Failure modes

`THREAT_MODEL.md` catalogues 17 failure modes across mathematical,
process, operational, and external categories, plus 2 cascade
scenarios. Most relevant to current external readers:

- **Mathematical 1.4**: the continuum-trick caveat (§1.2 above)
  could be externally embarrassing if the project announces
  "Clay-grade endpoint" without the qualifier. **Mitigation**: the
  qualifier is now in `STATE_OF_THE_PROJECT.md`,
  `MATHEMATICAL_REVIEWERS_COMPANION.md`, `MID_TERM_STATUS_REPORT.md`,
  `README.md` §3 (this session), and (consolidated here) in §1.2 of
  this file.
- **Mathematical 1.1**: the BK estimate could turn out tighter or
  looser than the blueprint claims. **Mitigation**: the blueprint
  has a risk register and alternative formulations.

---

## 8. How to verify any claim in this document

For each numbered item above:

- **Lean theorems**: `lake build YangMills` and `#print axioms <name>`.
- **Cited findings / audits**: read the linked file in this
  repository.
- **Bibliographic claims**: cross-check via `REFERENCES_AUDIT.md`
  and primary sources.
- **Codebase claims** (file paths, line counts, importer counts):
  reproducible via `git grep`, `wc -l`, `find`.

---

## 9. Late-session caveats (post-v1.85.0, 2026-04-25 evening)

After this document was originally drafted on 2026-04-25 morning,
two large pushes during the same day's late session added
substantial scaffolding to the project. Per **Findings 011–016** in
`COWORK_FINDINGS.md`, the following caveats apply to work added
after v1.85.0:

* **Finding 011** — At SU(1) every named OS-style structural axiom
  (`OSCovariant`, `OSReflectionPositive`, `OSClusterProperty`,
  `HasInfiniteVolumeLimit`) admits an unconditional inhabitant. This
  is structurally honest but physically vacuous: SU(1) is the
  trivial group `{1}`, so the witnesses do not say anything about
  SU(N) Yang-Mills for `N ≥ 2`.

* **Finding 012** — Same caveat extends to the Branch III analytic
  predicate set (LSI, Poincaré, clustering, Dirichlet form,
  Markov-semigroup framework) and the Feynman-Kac bridge.

* **Findings 013–014** — The Bałaban predicate carriers
  (`BalabanHyps`, `WilsonPolymerActivityBound`,
  `LargeFieldActivityBound`, `SmallFieldActivityBound`) are
  **structurally trivially inhabitable for every `N_c ≥ 1`** via
  zero / identity / vacuous witnesses. The genuine analytic content
  lives outside these carriers, in the composition with concrete
  physical Wilson Gibbs data.

* **Finding 015** — Codex's BalabanRG/ push (~222 files, 0 sorries,
  0 axioms) scaffolds the entire Branch II chain to
  `ClayYangMillsTheorem` with **trivial-witness placeholders** at
  every layer. Codex's own file comments
  (`RGContractionRate.lean` lines 70–82) acknowledge that the
  trivial witnesses must be upgraded to genuine RG dynamics for
  substantive Clay closure.

* **Finding 016** — `ClayCoreLSI` (the central LSI-named predicate
  of Codex's BalabanRG chain) is **not** the integral form of the
  log-Sobolev inequality; it is an arithmetic existential
  triviality. The substantive log-Sobolev content is concentrated
  in `ClayCoreLSIToSUNDLRTransfer d N_c` (the analytic bridge to
  the genuine `DLR_LSI` predicate from `LSIDefinitions.lean`).

**Combined late-session implication**: the Branch II analytic
obligation has been **localised** to a single structure
(`ClayCoreLSIToSUNDLRTransfer.transfer` for `N_c ≥ 2`). This is a
clarifying milestone, **not** a retirement of substantive work.
The literal-Clay % bar (~12 % per `README.md` §2's strict-Clay row)
is **unchanged**.

**Reference**: `COWORK_FINDINGS.md` Findings 011–016;
`COWORK_SESSION_2026-04-25_SUMMARY.md` §14.x; Cowork Phases 49–73
in this session.
  reproducible via `git grep`, `wc -l`, etc.

This document does not introduce any new claims — it consolidates
existing ones from the linked documents.

---

## 10. Post-Phase 463 caveats (added Phase 466)

The 2026-04-25 Cowork session continued through 466+ phases producing extensive structural output. Late-session caveats:

### 10.1 None of the late-session output has been built

The session produced 38 long-cycle Lean blocks (L7-L44, ~322 files), 18 Mathlib-PR-ready files in `mathlib_pr_drafts/`, and 22 surface docs **without running `lake build`** at any point during the session. The workspace lacks `lake`. Code may type-check; **none has been verified to do so**. See `BUILD_VERIFICATION_PROTOCOL.md` for the verification protocol when build access is available.

### 10.2 Two sorry-catches occurred and were resolved by hypothesis-conditioning

- **Phase 437 (L43)**: `polyakov_invariant_iff_zero` reached for `Complex.exp` periodicity. **Resolution**: hypothesis-conditioned with `ω ≠ 1` as input; later **closed at Phase 458** via `Complex.exp_eq_one_iff` + `Int.le_of_dvd` in `CenterElementNonTrivial.lean`.
- **Phase 444 (L44)**: `genusSuppression_asymptotic_zero` reached for `Filter.Tendsto`. **Resolution**: replaced with uniform bound `≤ 1/4`; later **drafted at Phase 461** in `AsymptoticVanishing.lean` (pending build verification).

The 0-sorry discipline caught both over-reaches immediately. Hypothesis-conditioning preserved the physical content. Both are documented in `COWORK_FINDINGS.md` Findings 022 + 023.

### 10.3 The triple-view characterisation (L42 + L43 + L44) is structurally complete but substantively empty

Each of L42 (continuous view), L43 (discrete view), L44 (asymptotic view) inputs dimensionless constants (`c_Y`, `c_σ`, `ω ≠ 1`) **as anchor structures, NOT derived from first principles**. The substantive proof of their equivalence requires the actual SU(N) Yang-Mills measure analysis, which the project does not yet provide.

**Implication**: when describing the project externally, the triple-view characterisation is **structural Lean scaffolding**, not a substantive advance. The Holy Grail of Confinement (Wilson area law from first principles) remains open since Wilson 1974.

### 10.4 The strict-Clay incondicional metric is unchanged at ~32% post-Phase 402

The metric advanced from ~12% to ~32% during the L30-L41 attack programme (Phases 283-402). Phases 403-466 (~63 phases) produced 18 PR-ready files + L42-L44 anchor blocks + 22 surface docs, **but no metric advance**. Structural / synthetic / contextual work does not retire named frontier entries.

### 10.5 P0 questions: 3 of 5 closed in-session, 2 require build environment

| P0 # | Status |
|---|---|
| §1.1 (Mathlib PR upstream) | open (requires `lake`) |
| §1.2 (`lake build` 38 blocks) | open (requires `lake`) |
| §1.3 (`centerElement N 1 ≠ 1`) | ✅ CLOSED Phase 458 |
| §1.4 (asymptotic `→ 0`) | 🟡 DRAFTED Phase 461 (pending build) |
| §1.5 (update MID_TERM) | ✅ CLOSED Phase 462 |

The 3 in-session closures (Phases 458, 461, 462) constitute the **P0 closure mini-arc** documented in Finding 024.

### 10.6 The 18 PR-ready files have NOT been built; expect tactic-name drift

Each file in `mathlib_pr_drafts/` is a **math sketch + Lean draft**, not a verified contribution. Tactic-name drift (`pow_le_pow_left` → `pow_le_pow_left₀`, `lt_div_iff` → `lt_div_iff₀`, `Real.log_div` argument order, `Real.exp_nat_mul` argument swap) is real and will require non-trivial polishing per file. See `MATHLIB_SUBMISSION_PLAYBOOK.md` for guidance.

---

## 9. Last refresh + ownership

**Last refreshed**: 2026-04-25 by Cowork agent.
**Refresh policy**: regenerate when any of the following change:
- A new finding is filed in `COWORK_FINDINGS.md`.
- A finding's status changes from open to addressed.
- A new caveat is documented in any strategic doc.
- The audit pass surfaces a new known issue.

If you find an issue not in this document but documented elsewhere,
file a finding (`COWORK_FINDINGS.md`) and request a refresh of this
file in the next Cowork session.

---

*Consolidated public-facing known-issues summary, 2026-04-25.*
