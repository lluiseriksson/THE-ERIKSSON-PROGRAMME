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
   incremented** (currently 8250).

## The autonomous loop

Work in campaigns (design doc in `docs/`, brick ladder, per-brick
oracle checks). After each green checkpoint: update
`docs/VERIFICATION-LEDGER.md` (+ the campaign plan, `README-FOR-NEXT-MODEL.md`,
`HYPOTHESIS_FRONTIER.md` if touched), commit, push, pick the next
highest-leverage target, continue. Do not wait for confirmation.

## Build & verification mechanics (Windows host)

* Toolchain: `leanprover/lean4:v4.29.0-rc6`, Mathlib master (pinned by
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

## Current state (2026-06-12)

* Core green: **8238 jobs**, zero sorry, zero axioms.
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
* Other frontiers: Peter–Weyl; the §6.3 UV bound.
