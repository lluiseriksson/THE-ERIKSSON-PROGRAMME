# CLAUDE.md — standing instructions for any model working in this repo

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
  `cef5ffb3948655574e64084a92e03913d11a76d3`.  See
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
