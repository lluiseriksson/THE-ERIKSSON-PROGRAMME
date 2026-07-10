# CLAUDE.md — standing instructions (one repo, two programmes)

This repo hosts TWO programmes. PART I is the Surface Theorem closure
(the paper track): ACTIVE and prioritized by owner instruction of
2026-07-10 — read it first and work its task queue. PART II is the
Yang–Mills Lean formalization programme: its rules remain binding for
any work under YangMills/**, and it is precisely the “claimed bridge”
that Part I’s Yang–Mills instruction says must be audited link-by-link
(after the paper ships) before any importance transfers.

---

# PART I — SURFACE THEOREM CLOSURE (paper track — ACTIVE, owner priority 2026-07-10)

Hash rule: every relay/commit message carries its hash context on the
first line. Read this file FIRST, then docs/SURFACE-CLOSURE-NOTES.md
(the acta, v1–v48 — the single source of truth; when anything
diverges, THE MOST RECENT HASH RULES).

## What this is

An audit-first mathematical research programme closing the SURFACE
THEOREM: for all beta > 0, (i) F_B > 0 on (0, pi) [proved twice] and
(ii) E' < 0 on (0, pi) [relay in progress]. The live manuscript is
papers/surface-complete/surface_theorem_complete.tex (+pdf, always
same commit). DO NOT SUBMIT while any [SLOT] lives.

## REGIME (non-negotiable, before any work)

1. TRICOTOMY everywhere: "exact" only with proof; "certified" only
   with a committed interval-arithmetic transcript; "verified" for
   numerics. No label upgrades without its witness.
2. Every number travels with (convention, t, beta). Convention:
   integrals over [-pi,pi]^2 unnormalized (conv:mass in the paper).
3. JUDGES BEFORE PAGES: no intermediate target is used unless its
   own pre-registration passed. Standing judges (notes v40–v48):
   - EXTERIOR: beta·X -> T(c) = (1/2 - 1/(8c^2))/c on nine
     pre-registered cells; R_1(c) must land in [residual, 3x] with
     residuals 0.101–0.292; stress cell (2.9, 15) judged in two
     pieces (saddle +0.023553; mirror -0.0707 vs derived M).
   - PARTIAL: beta·X_1 -> 2T(c) (frozen-ratio, single measure K);
     beta·X_2 -> -T(c) (ratio-variation, deficit-weighted).
   - L CROSS-TABLE: finite-difference L's must match the series
     table within +-25% cell by cell (v44).
   - FACTORY tolerances: x2 first-order moments, x3 masses, x10
     remainders (v37/v38 context).
   - RECEPTION of THE page: five marks IN ORDER, stop at first
     failure (v43).
4. SPLIT ROLES, mandatory: one session FABRICATES, a DIFFERENT
   session AUDITS against the judges before merging. Never both in
   one session.
5. Measured failure = commit with diagnosis. Never delete. (See
   derive_page_attempt1.py and notes v45–v46.)
6. Constants: only DERIVED constants go to ink; benches calibrate
   (ghost #23 rule).
7. Long runs: absolute script paths (ghosts #20/#21), frozen run
   clone, transcripts do not exist until committed, iteration caps
   (ghost #22), ball+boolean in every printed enclosure, provenance
   header (script sha256, library versions, stage parameters).
8. Symbolic tooling (class rule, protocol desk 2026-07-10): NO
   sympy.series() in load-bearing symbolic work - it fabricates
   spurious rational functions of the integration variables
   (measured twice in the pass-2 session). Polynomial arithmetic
   with explicit truncation and explicit geometric reciprocals.
9. Git staging is EXPLICIT (class rule, same round): never
   'git add -A' while concurrent sessions work the same clone -
   it sweeps other desks' in-progress files into your commit.

## WHERE EVERYTHING IS

- Repo: github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME (branch main).
- Acta: docs/SURFACE-CLOSURE-NOTES.md (v1–v48; ghosts #1–#25 with
  mechanisms and the rules they bought).
- Manuscript: papers/surface-complete/surface_theorem_complete.tex.
  Slots remaining: [6,15] coverage row, analytic relay [15,inf),
  sinc-cert, pi-window 4 constants, header theorem seal.
- Scripts (scripts/): exp_integrator_arb.py (DEFINITIVE integrator,
  sha256 834802f9... post ghost-#25; nesting assert; design table);
  exp_integrator_arb_RUN_1d888e99.py (pinned bytes of the harvest
  run); harvest_arb_transcript_1d888e99.txt (the certified local box
  transcript: point/stability/3x3 box all True, 22,986,387 cells);
  test_safe_sqrt.py (7 cases, arb-ball containment); margin_map_*
  (design-only, labeled); derive_page_attempt1.py (failed pass 1,
  archived); ERRATUM-display-supersets.md.
- Local machine (Lluis's Windows box): run clone
  C:\Users\lluis\AppData\Local\Temp\eriksson-push (FROZEN for git
  ops while runs live), push clone ...\eriksson-push2, python
  C:\Python312\python.exe (mpmath, sympy, python-flint 0.9.0).
  Oven outputs in C:\Users\lluis\AppData\Local\Temp\
  (margin_map_fine_out.txt, margin_map_probes_out.txt).
- Governance frozen at commit f2ea0d0: coverage witness = exhaustive
  Arb + independent sampled implementation audit (2%, seed =
  SHA256(f2ea0d0-ASCII | box-id), box-id = exact rational coords;
  ONE mismatch = full stop + autopsy).

## TASK QUEUE (strict order)

1. PASS 2 of THE PAGE (bilinear saddle extraction lemma): extract
   X_1 (pure-K bilinear r(z_s)[<D><ND> - <N><D^2>], five v5-templated
   moments) against judge 2T(c); then X_2 (deficit-weighted moments,
   bilateral root floor) against -T(c); sum against the exterior
   judge; Lagrange remainders citing the two-term companions (v40:
   |eps_1| <= 0.6/z^2, |eps_0| <= 0.4/z^2, R_2 <= 2.12 u^4). The
   X_2 = -X_1/2 shortcut is CANCELLED (asymptotic only, v48). On
   pass: ink to manuscript + tooth restored SAME COMMIT.
2. MECHANICAL CASCADE: minoration via mu_D = 2mu_1 - 4mu_P (exact,
   v35 — mu_1's integrand is positive, nothing to subtract);
   C-hat assembly against the 0.42 piece-A budget with the
   eight-cell law as lock; Region II (= the layer lemma, spec v32);
   splices; explicit beta_0 with the negotiation rule (analytic
   margin >= 2x consumed, machine absorbs [15, beta_0]).
3. OVEN: L matching (+-25% vs v44 table) -> pilot at dz ~ 0.25 with
   dz(beta) scaling -> full [3,15] campaign under frozen governance.
   If Lluis authorizes cloud: parallelize by beta ranges,
   concatenated transcripts with hashes.
4. EDGES: sinc-cert on (0, t*(beta)] x [3, beta_0] (exact sinc
   lemma is in the paper; minor criterion + tail m+n > pi/t +
   uniform overlap pending); pi-window 4 constants (c_3 as a cheap
   1D passenger in the harness).
5. MANUSCRIPT: replace each [SLOT] the day its piece closes; relay
   table without amber (thmB iv canonical + bulk iv resume from
   beta = 5.7305 are pending second witnesses); PDF+tex same commit.
6. SUBMISSION: arXiv math.CA (or JMAA direct), the complete paper,
   ghost ledger included. NOTHING is called final with a live slot.

## ON "ITERATE TO YANG–MILLS" (the honest instruction)

There exists NO proved reduction from the Surface Theorem (or
anything in these repos) to the Yang–Mills mass-gap problem. The
instruction is NOT "iterate toward YM" — that order produces
adjacent theorems with grandiose names, the exact trap this
programme learned to avoid. The correct sequence:
(a) finish and submit THIS paper;
(b) survive the referee — the first real external calibration,
    worth more than any plan;
(c) if the repos contain a chain claiming to connect to YM, the
    next work is auditing that chain LINK BY LINK under this same
    regime, starting from the weakest link, presuming it dies there
    (millennium programmes die at the bridge, not in the lemmas);
(d) only if a bridge link survives adversarial audit, build the
    next theorem THAT LINK demands — never the one ambition
    suggests.
Permanent honesty criterion: importance is not inherited by
thematic proximity; only a proved reduction transfers it. An agent
that respects (a)–(d) will advance whatever is mathematically
advanceable; one that jumps to (d) without (c) will manufacture
seventy more papers of fog.

## THE OWNER

Lluis decides what is submitted and when. That role is not
delegable. Bring him the complete manuscript when it exists.

---

# PART II — YANG–MILLS LEAN PROGRAMME (standing rules, preserved verbatim)

This file is read automatically by Claude-family agents. It replaces the
old `.claude/agents/` directory (deleted 2026-06-12: it described an
OpenRouter/Colab workflow and a vacuous-target strategy that no longer
exist). The complete operational brief is `README-FOR-NEXT-MODEL.md`;
read it before editing anything. This file is the non-negotiable core.

## The defining principle

**Honesty over progress.** A smaller true claim always beats a larger
hollow one. The repository's history contains a vacuous terminal
theorem (`∃ m > 0`); the entire point of the current programme is to
never repeat that.

## Hard rules (no exceptions)

1. **No `sorry`.** Anywhere, ever, in committed code.
2. **No project axioms.** Gaps are carried as explicit theorem
   *hypotheses*, never as `axiom` declarations.
3. **No vacuous weakening.** Never restate a target so that it becomes
   trivially true. Adversarially audit your own statements for
   vacuity (non-emptiness witnesses, non-trivial instantiations).
4. **Oracle every headline.** `lake build YangMillsCore` must be green
   and `#print axioms` on every headline result must print exactly
   `[propext, Classical.choice, Quot.sound]`.
5. **Never push broken code.** Commit only from a green checkpoint.
6. **Keep the Clay distance honest.** Every status document states
   ~0% (<0.1%) distance to the Clay problem until the continuum
   limit / OS reconstruction exist on paper. Never claim Clay progress
   without naming the reduced obstruction.
7. **After adding a module to the core, confirm the build job count
   incremented** (latest recorded checkpoint: 8369).

## The autonomous loop

Work in campaigns (design doc in `docs/`, brick ladder, per-brick
oracle checks). After each green checkpoint: update
`docs/VERIFICATION-LEDGER.md` (+ the campaign plan, `README-FOR-NEXT-MODEL.md`,
`HYPOTHESIS_FRONTIER.md` if touched), commit, push, pick the next
highest-leverage target, continue. Do not wait for confirmation.

## Build & verification mechanics (Windows host)

* Toolchain: `leanprover/lean4:v4.29.0-rc6`, Mathlib pinned to
  `07642720480157414db592fa85b626dafb71355b` (`lakefile.lean` +
  `lake-manifest.json`). Build: `lake build YangMillsCore` (~minutes
  when cached). Oracle: `lake env lean oracle_check.lean`.
* Long builds: detached
  `Start-Process powershell … | Out-File log + sentinel-file` pattern,
  poll in ≤45 s slices. `$` gets stripped by some shells — put
  PowerShell in `.ps1` files and run with `-File`.
* **Never edit repo files through the Linux mount for large
  rewrites** — the mount desyncs and truncates files. Do file surgery
  Windows-side (python script files, `git checkout --` to recover).
  Never run git from the mount.
* Scratch debugging files (`_*.lean`, `_*.ps1`, `_*.py`) are
  fine *uncommitted*; delete before committing. `sorry` is allowed in
  scratch files only.

## House proof-engineering idioms

The accumulated Lean/Mathlib battle notes (whnf hangs with symbolic
`∏`, `letI` in binder types, expected-type-driven application of
`integral_tsum_of_bounded`, `Summable.`-namespaced tsum lemmas, …)
are recorded **in the campaign plans** — primarily
`docs/AREA-LAW-EXACT-PLAN.md` §2 (house notes per closed brick) and
`README-FOR-NEXT-MODEL.md`. Read them before writing analysis-flavoured
Lean; they save hours.

## Current state (updated 2026-07-04; source checkpoint 2026-07-04)

* Latest recorded core checkpoint: **8369 jobs**, zero sorry, zero axioms.
  Mathlib **pinned** to an exact commit (lakefile + manifest agree); the
  ledger includes the earlier Addendum 444/date-stamped checkpoint material
  plus the 2026-07-03 Catalan/Schur series through Addendum 257 and the
  2026-07-04 diamagnetic unitary bridge Addendum 258; current `origin/main` is
  `0919aa10`.  See
  `REPRODUCIBILITY.md`.
* Read `CURRENT-STATE.md` first.  It is the short live checkpoint; the long
  campaign docs are historical/auditable detail.
* **`hRpoly` campaign OPEN** (`docs/HRPOLY-CAMPAIGN-PLAN.md`): the sole
  remaining analytic input of the §6.3 UV conditional.  The theorem-fed
  substrate now includes animal counting, cube summability, marginal-coupling
  summability, exponential-decay kernel calculus, Schur bounds, PSD kernels,
  Gaussian MGF bounds, finite-dimensional Gaussian construction, explicit
  shell-growth summability, source-only UV routes, YM activity error-budget
  records, finite-carrier/profile wrappers, animal-summability bridges,
  Appendix-F certified-tail/source-fed residual routes, Wilson-Hessian/Green
  source dictionaries, CMP119/CMP122 E/R/B decomposition interfaces, CMP119
  B/local source-bound and weight-transport dictionaries, B/local
  metric/rate/amplitude/activity dictionary frontiers, Eq. (2.31) `gapCubes`
  candidate definitions, source-db proof-obligation cards and
  hypothesis-removal queues, canonical-root K# and residual H# adapters, the
  flow-diamagnetic UV branch's marginal-coupling, killed-walk,
  block-transport, factorial-kernel substrate, finite unitary-to-isometry
  bridge, the Catalan majorant / Schur-budget / physical-precision covariance
  lane, and the KP activity-domain zero-free polydisc.
  The open work is the concrete YM
  cluster-expansion-with-holes activity-decay estimate for the actual gauge RG
  operator (`hRpoly`): gauge-covariant operator, background-field minimizer,
  propagator decay, localization, and raw activity bound.
* **Gauge-RG continuum-facing track (`YangMills/RG/**`, ledger Addenda
  23–444):** local averaging/Gaussian/kernel/combinatorial substrate,
  marginal-coupling summability, Appendix-F/H# consumers, integrated
  second-gas adapters, coercivity-budget bricks, gauge-fixed precision
  and covariance composition, physical gauge cochains, flat Hodge/block
  Poincare bridges, the finite-torus curl/divergence classification,
  source-facing covariance/root localization APIs, a local
  fluctuation-activity certificate, generic/CMP116 `K#`/`H#` and second-gas
  dependency wrappers, cluster-union containment facts, exact CMP116
  local-operator support algebra, physical/CMP116 coordinate dictionaries,
  localized-root transport, dictionary-backed Gaussian/activity construction,
  canonical Gaussian integral consumers, raw-source transport into CMP116
  `hraw`, scale-indexed raw-source H# consumers, raw-source M3 frontier
  bundles, an executable M3 frontier dependency graph, source-assumption
  packaging into that frontier, the source-facing Balaban CMP116 theorem
  target, CMP116 Lemma 3 activity-only estimates, Eq. (2.29) consumers,
  Eq. (2.31) weighted `P`-stage and post-`P` raw-source M3 routes,
  residual-stage bridges, P-stage and `Z0` source-budget adapters, Eq. (2.31)
  source-membership/projected-carrier/positive-tail/interior-boundary routes,
  Gaussian source-record package constructors, combined post-`P` source
  packages, visual Eq. (2.37)/C3 citation extraction, the public `source-db`
  frontier/artifact lookup layer, the resolvent-first local SPD precision
  substrate, local-SPD root frontier packaging, dictionary root-map norm
  budgets, finite-piece root sums, finite-family physical activity consumers,
  source-only UV decay endpoints, finite-carrier/profile wrappers, hRpoly
  animal-summability bridges, Appendix-F certified-tail profiles, source-rate
  weighted-tree extraction, source-fed residual estimates, Wilson-Hessian/Green
  source dictionary packaging, CMP119/CMP122 E/R/B source-decomposition
  interfaces, CMP119 B/local source-bound and weight-transport dictionaries,
  B/local metric/rate/amplitude/activity dictionary frontiers, Eq. (2.31)
  `gapCubes` candidate definitions, source-db proof-obligation cards and
  hypothesis-removal queues, canonical-root K# summability/smallness discharge,
  the source-facing canonical-root residual H# route, the flow-diamagnetic
  UV branch's marginal-coupling, killed-walk, block-transport,
  factorial-kernel substrate, finite unitary-to-isometry bridge, the Catalan
  majorant / Schur-budget / physical-precision covariance lane, and the KP
  activity-domain zero-free polydisc are oracle-clean.
  The branch remains lattice/M3-side and conditional on
  `hRpoly`; M4/M5/Clay are untouched.
* Done: sharp KP, Mayer–Ursell `Ξ = exp(clusterSum)`, `Z = Ξ`, the IR
  clustering bound (B4), the two-plaquette correlator decay (T4), the
  finite-volume area law (linearized, AL1–AL6), the
  **exact-activity area law** (`finite_volume_area_law_exp`), and the
  **VOLUME-UNIFORM AREA LAW** — the VU campaign
  (`docs/AREA-LAW-VU-PLAN.md`, V0–V3) is **CLOSED** (ledger Addenda
  17–17t).  Headline: `normalized_wilson_loop_area_law`
  (`L1_GibbsMeasure/RestrictedGate.lean`) —
  `‖(∫ tr W_C·∏(1+f))/Z‖ ≤
  N_c·e^{#loopSupp·4d·K}·σ^{Area(C)}·e^{#loopSupp·4d·S(σ)}`,
  every constant volume-free, `Z` cancelled through the restricted
  cluster expansion; non-vacuity audited (Addendum 17t).  The
  integrability families are DISCHARGED (Addendum 17u):
  `normalized_wilson_loop_area_law_unconditional` carries only
  explicit, jointly satisfiable smallness/geometry hypotheses.
* M3 assembly: IR side theorem-fed; the §6.3 Balaban UV single-scale
  bound is the **sole carried hypothesis**.
* **V4 CLOSED** — the VU area law for the TRUE Wilson factor
  `∏exp(z_p)` (`docs/AREA-LAW-VU-PLAN.md`, ledger Addenda 18–18d).
  Headline: `normalized_exp_wilson_loop_area_law`
  (`L1_GibbsMeasure/RestrictedGate.lean`) —
  `‖(∫ tr W_C·∏exp(z_p))/Z‖ ≤
  N_c·e^{#loopSupp·4d·K}·σ^{Area(C)}·e^{#loopSupp·4d·S(σ)}` for the
  exact Wilson factor at the conjugate pair, every constant
  volume-free, NO integrability hypothesis families (only explicit
  smallness/geometry).  Built by mirroring the linearized headline
  with the single substitution `2δN_c → e^{2δN_c}−1` — the generic
  V0/V1 machinery is activity-agnostic, so only the per-pinned
  dichotomy (`norm_integral_exp_pinned_term_le`) changed.
* Other frontiers: Peter–Weyl completeness; the concrete `hRpoly` source
  theorem inside the §6.3 UV bound.
