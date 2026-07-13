# C6 CHARTER — "The correlator bridge: anchoring the M3 assembly to
# the Wilson measure" (registered 2026-07-13, BEFORE any fabrication)

Owner order (2026-07-13, in-session): attempt route (a) of the
M3 bridge audit (docs/M3-BRIDGE-AUDIT-20260713.md, commit 760dd9a8)
targeting 8/10 on the absolute scale, while a second desk ("Sol")
works the hRpoly activity ladder (b) and the Surface queue (c).
All Part II hard rules bind (no sorry, no axioms, no vacuous
weakening, oracle every headline, job-count witness).  All C1-C5
lessons bind (amendments/charters in OWN commits before the work
they govern; explicit staging; ASCII-only .ps1; hash rows from git
show, never worktree bytes).

## COORDINATION (registered now)

This lane works in NEW modules only: `YangMills/RG/CorrelatorBridge*.lean`
(+ one import line in the core root and an appended oracle block).
It does NOT touch the hRpoly lane files (`YangMills/RG/Physical*`,
AppendixF*, Catalan*) that the concurrent desk owns.  Fabrication
happens in the isolated short-path clone `C:\Temp\c6bridge`; pushes
are rebase-first; if the root/oracle collide with the other desk's
push, resolution preserves BOTH desks' additions (pure-addition
merges only).

## What the audit established (inputs, verbatim pointers)

- The M3 assembly (`lattice_mass_gap_of_cluster_and_marginal_coupling`,
  `YangMills/RG/MarginalUVMassGap.lean:111`) quantifies over FREE
  abstract `covIR, Rsc, g, nsc`; nothing identifies
  `covIR + covUV_concrete` with the two-point function of the
  actual SU(N) Wilson Gibbs measure.  The identification is
  instantiation freedom — the audit's weakest link (50-60% of the
  remaining distance to M3-unconditional-at-weak-coupling).
- The proved IR input (`gibbs_truncated_correlation_bound`,
  KP window) is STRONG-coupling; the hRpoly UV programme is
  WEAK-coupling.  Regime coherence for a single measure is open —
  and in the honest multiscale picture the IR input should apply to
  the EFFECTIVE theory at the terminal RG scale (asymptotic
  freedom grows the effective coupling into the KP-treatable
  regime), not to the original measure at the same beta.
- Score realism (C5 = 6.00 anchor): the 7.3-8.0 band exists ONLY
  for: bridge formulated + proved against the concrete measure +
  volume-uniform + regime-coherent.  Risk-weighted 6.3-7.2; kill
  risk 50-70%.  THE 8 IS A CEILING, NOT A PROMISE; every phase
  below states what it alone is worth.

## Phases, judges, budgets

- **Phase B-1 (FORMULATION; this charter's first fabrication):**
  new module `YangMills/RG/CorrelatorBridge.lean`:
  (i) `structure CorrelatorBridge (covPhys : N -> R)` — covIR, Rsc,
  nsc + the DECOMPOSITION IDENTITY `covPhys t = covIR t +
  covUV_concrete Rsc nsc t` as a field (the identity that today
  exists nowhere);
  (ii) the consumer theorem `physical_mass_gap_of_bridge`: for ANY
  covPhys, a bridge + IR bound + `SingleScaleUVDecay` + marginal
  flow => `∃ gap > 0, |covPhys t| <= C e^{-gap t}` — the FIRST
  statement in the tree whose conclusion is about the (arbitrary,
  then physical) correlator function itself;
  (iii) the PHYSICAL anchor: instantiate covPhys at the tree's
  actual SU(N) Wilson two-plaquette truncated correlator (the
  object of `sun_two_plaquette_correlator_bound`) and name the
  frontier `WilsonCorrelatorBridge` — converting the audit's
  "unformulated" verdict into named, typed hypotheses;
  (iv) NON-VACUITY witness: the trivial bridge (covIR := covPhys,
  Rsc := 0) discharges all hypotheses at strong coupling via the
  PROVED clustering window, yielding the physical-correlator decay
  through the bridge — witness that the structure is inhabited and
  the consumer fires; the accompanying remark states honestly that
  the trivial bridge carries no UV content (no novelty claim).
  JUDGE J-C6-1: build green (+job increment), oracle extended and
  clean, non-vacuity witness compiled, ZERO new axioms/sorry;
  adversarial self-audit that no statement is vacuously weakened.
  Value alone: formalization brick (~5-5.5 absolute) + kills the
  "scaffolded decomposition" referee objection structurally.
  Budget: 3 attempts.
- **Phase B-2 (THE REGIME GATE; the research risk):** formulate
  `RegimeCoherentBridge` — a bridge for the Wilson correlator with
  NONTRIVIAL UV part whose IR and UV hypotheses hold simultaneously
  — in the SCALE-INDEXED form (IR bound at the terminal effective
  scale, not the original beta), and attack existence: (i) desk
  derivation of the effective-coupling window; (ii) either a
  constructive window (=> the 7+ milestone stays alive) or a
  machine-checked OBSTRUCTION theorem (single-beta incompatibility
  of the current inputs — publishable negative result, ~6-6.5).
  JUDGE J-C6-2: external evaluator verdict on whichever branch
  closes.  Budget: 3 attempts, then honest report.
- **Phase B-3 (conditional):** only if B-2 survives constructively:
  volume-uniformity + the activity ladder junction (coordinated
  with the hRpoly desk).  This is where 7.3-8.0 lives; it is NOT
  promised.

## Kill criteria (registered now)

- B-1 fails to state the decomposition without new axioms => stop,
  diagnose, re-register.
- B-2 obstruction branch closes => the 8-target via this chain is
  DEAD; the charter converts to the obstruction paper + handoff of
  the demanded reformulation; no silent pivot to adjacent theorems.
- Any statement found vacuous at audit => same-commit retraction.

## Score ladder (pre-registered, absolute scale)

B-1 alone ~5-5.5; B-1 + B-2 obstruction ~6-6.5; B-1 + B-2
constructive window ~6.5-7.0; full B-3 milestone 7.3-8.0 SUBJECT to
surviving external referee (50-70% kill risk on record).  No number
is claimed in any paper without its external verdict.
