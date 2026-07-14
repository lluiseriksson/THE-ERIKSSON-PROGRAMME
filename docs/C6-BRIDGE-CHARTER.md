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

## AMENDMENT 1 (2026-07-13, own commit, pre-B-1' — external verdict
4.60/10 on B-1 as shipped + THE GAMEABILITY COUNTEREXAMPLE, accepted)

VERDICT RECORDED: **4.60/10 absolute** on the B-1 artifact alone
(below the registered 5-5.5 band — calibration miss noted).  Credit
granted: the bridge converts an implicit identification into a
formal hypothesis; the consumer concludes about covPhys itself; the
correlator uses the genuine Wilson measure; the module is honest
about proving no new estimate; oracle intact (1945).

THE ACCEPTED DEFECT (evaluator's counterexample, verbatim
substance): `RegimeCoherentWilsonBridge` requires only a scalar
decomposition + a bound on Rsc + SOME nonzero Rsc t k.  From the
already-proved strong-coupling decay one can fabricate
  R_{t,0} = a e^{-t},  R_{t,k} = 0 (k>0),
  covIR t = covPhys t - a e^{-t},  nsc t = 1,
satisfying every field with ZERO ultraviolet/RG content.  The
"nontrivial UV part" field does not certify UV PROVENANCE; the Prop
does not yet represent the open question its docstring names.
Further accepted: the main new theorem is logical transport; the
strong-coupling witness reuses the decay it assembles; the ray
correlator is a finite-torus object ("mass-gap-shaped" is the only
permitted phrasing); there is no C6 paper yet.

AMENDED B-2 TARGET (registered now, before fabrication — the
evaluator's own prescription adopted as the specification):
RG PROVENANCE.  B-1' must build, in order:
1. **Effective family**: per-scale effective correlators arising
   from a CONCRETE RG map on the Wilson theory — a defined
   block/decimation transformation `T` acting on the finite-torus
   gauge measure (pushforward), with `mu_0` = the Wilson Gibbs
   measure and `mu_{k+1} = T(mu_k)`, and the transported observable;
   `covEff k` = the truncated correlator OF mu_k, BY DEFINITION —
   so the family cannot be chosen freely.
2. **Telescoping identity as a THEOREM, not a field**:
   `Rsc t k := covEff k t - covEff (k+1) t`,
   `covIR t := covEff (nsc t) t`; the bridge decomposition then
   HOLDS by telescoping — `Rsc` is PRODUCED, not selected.
3. **The gate, re-stated**: `RGProvenantBridge` = the bridge whose
   fields are DEFINED from (1)-(2); the open question becomes the
   two bounds for THAT `Rsc` and THAT `covIR` — which is exactly
   the honest mathematical frontier (fluctuation integration =
   G5-adjacent), no longer gameable by re-labeling known decay.
4. The old `RegimeCoherentWilsonBridge` is RETAINED with a
   docstring correction (it is a NECESSARY interface, not the open
   question) — no silent deletion.
SCORE LADDER UNCHANGED except honesty note: B-1-as-shipped measured
4.60; the >6 threshold requires (1)-(3) delivered; 7+ additionally
requires a NEW nontrivial estimate in a relevant uniform regime.
Budget: B-1' = 3 attempts.  Kill criteria unchanged.

## AMENDMENT 2 (2026-07-13, own commit, pre-B-1'' — external verdict
4.85/10 on B-1' + THE SINK-FLOW COUNTERATTACK, accepted; TWO CLAIMS
RETRACTED)

VERDICT RECORDED: **4.85/10 absolute**.  Credit: telescoping layer
correct (covEff from the per-scale measure, provenantRsc as literal
consecutive differences, decomposition a theorem, scale zero
anchored, old gate honestly reclassified).

RETRACTIONS (mandatory, registered here; the B-1' commit message and
Addendum 482 carry the overclaims, immutable — THIS amendment is the
correction of record):
1. "Amendment-1 spec delivered, no fallback" is WITHDRAWN: item 1
   demanded a CONCRETE blocking/decimation transformation acting as
   pushforward with a transported observable; what shipped is
   `step : Measure X -> Measure X` with NO property (not pushforward,
   not probability-preserving, no locality, no gauge covariance, no
   coarse lattice, no observable transport — covEff uses the same f
   and the same fine GaugeConfig at every scale).  An abstract
   measure family was delivered, not an RG family.
2. "Anti-gaming" is WITHDRAWN: `step_moves_of_provenantRsc_ne_zero`
   certifies non-stationarity only, not RG provenance.

THE SINK-FLOW COUNTERATTACK (accepted verbatim substance): take
T(nu) = 0 for every nu (or a fixed Dirac — connected correlator
zero, so probability preservation alone would not help), F =
ofStep(mu_W, T), nsc = 1: then covEff 0 = cov_W, covEff k = 0 for
k >= 1, provenantCovIR = 0, provenantRsc t 0 = cov_W t — the ENTIRE
physical correlator relabeled as first-scale UV remainder, its known
strong-coupling bound converted into SingleScaleUVDecay by adjusting
C2 by g(0)^{-kappa0}.  Same logical mechanism as the first
counterexample, one level up.  FURTHER ACCEPTED: the gate does not
even require provenantRsc nonzero (constantFlow proves it — the
docstring's open question is again not the typed Prop); and the
finite-torus ray correlator has finite support, so ANY function of
that shape admits SOME exponential bound at large enough amplitude —
volume-uniformity of the constants must enter THE STATEMENT, not a
later ornamental phase.

B-1'' SPECIFICATION (the evaluator's prescription adopted verbatim
as spec; >6 threshold requires ALL of it):
1. `ConcreteGaugeRGStep`: fine and coarse configuration spaces; a
   DEFINED blocking map (or Markov kernel); effective measure as
   pushforward (or conditioned integration) — BY CONSTRUCTION, not
   as a field; probability preservation; locality; gauge
   covariance; explicit observable transport across the scale
   change; the geometric scale relation.
2. Constants of both bounds UNIFORM IN THE TORUS SIZE, inside the
   gate statement itself (family over N, single constants).
3. `NontrivialConcreteRGWilsonBridge`: the gate quantifying ONLY
   over that concrete class, WITH the nonvanishing clause — noting
   (evaluator) that adding `Rsc != 0` to the abstract gate would
   NOT suffice (the sink flow satisfies it); nontriviality must be
   an emergent consequence of the concrete class + bounds.
4. No claim of "delivered" without an external verdict; the module
   docstring must carry the residual-risk inventory explicitly.
Budget: 3 attempts.  Kill criteria unchanged.  Score reality: the
6 barrier remains UNCROSSED; 4.85 is the measured state.

### Amendment 2 — TECHNICAL NOTE (registered before B-1'' fabrication,
own commit; two evaluator-prescribed design constraints, verbatim)

1. QUANTIFIER ORDER FOR VOLUME UNIFORMITY.  The gate must read
     exists C1 C2 eps ... , forall N, (bounds at torus size N)
   — constants FIRST, uniform over all torus sizes.  The form
   "forall N, exists C(N), ..." remains vulnerable to the finite
   support of each torus (any single-N function admits some
   exponential bound) and is FORBIDDEN in the gate statement.
2. NONVANISHING IS DATA-SPECIFIC, NOT CLASS-AUTOMATIC.  The concrete
   class `ConcreteGaugeRGStep` must exclude the sink flow BY
   PHYSICAL CONSTRUCTION (pushforward/conditioned integration of the
   given measure, probability preservation, locality, gauge
   covariance, observable transport) — but the nonvanishing of the
   produced remainder must STILL appear as an explicit clause for
   the specific flow, observable, and Wilson data considered.  Do
   NOT engineer the class so that membership implies Rsc != 0
   automatically: a genuine RG can have fixed measures or invariant
   observables, and forcing nonvanishing through the class would be
   a new vacuity-adjacent distortion in the opposite direction.

### Amendment 2 — VERDICT RULES FOR B-1'' (evaluator-fixed, registered
before the artifact exists; the fabrication desk builds against them)

1. One-step + two-scale bridge = PARTIAL FALLBACK, not full B-1''.
2. Gauge covariance / locality as named open lemmas = honest
   diagnosis, NOT delivered.
3. `Measure.map blockMap mu` must carry the necessary measurability
   hypotheses and a transport identity USABLE downstream (stated for
   the correlator shape the bridge consumes), not a bare
   `integral_map` wrapper.
4. Volume uniformity is checked IN THE TYPE of the Prop: constants
   quantified before every volume family.
5. The self-attack must exclude the four attacks STRUCTURALLY
   (typed theorems / type-level consequences); documentation-only
   exclusions count as partial evidence.
Frozen score pending the artifact: 4.85/10.

## AMENDMENT 3 (2026-07-13, own commit, pre-B-1''' — external verdict
5.75/10 on B-1'': FIRST VERSION WITH NO ARTIFICIAL INSTANTIATION
FOUND; the four self-attacks confirmed closed by the evaluator)

VERDICT RECORDED: **5.75/10** (from 4.85).  Delivered per the
evaluator: concrete transformation (sink/Dirac structurally closed),
pushforward by construction, proved covariance/locality/measurability,
usable transport, cast-free multi-scale tower, telescoping,
uniformity over the dyadic family in the type, data-clause
nonvanishing.  "The decisive limitation is no longer gameability but
INCOMPLETE PHYSICAL FIDELITY."

THE FIVE BLOCKERS OF 6 (accepted, spec for B-1'''):
1. UNIFORMITY IS DYADIC-COFINAL, NOT LITERAL forall-N: constants may
   depend on the outer M0; need either literal exists-C-forall-N or
   a TYPED justification that the dyadic family suffices for the
   thermodynamic limit.
2. METRIC TRANSPORT MISSING: concreteCovEff uses the same t at every
   scale; need the touchGraph distance identity under the coarse
   embedding (dist_{2M}(embed p, embed q) vs 2*dist_M(p,q)) and
   compatible transport of the selected plaquette pairs — without
   it the telescoping is algebra, not a scale decomposition of one
   physical separation.
3. RAY CORRELATOR TOO WEAK: Classical.choose pair; need sup over
   admissible pairs, a canonical geometric pair, or a typed
   translation-invariance argument making the choice irrelevant.
4. WILSON PROBABILITY INSTANCE NOT CONNECTED: the gate does not
   derive IsProbabilityMeasure for wilsonGibbsMeasure; supply the
   instance and thread it so the whole tower is typed probability.
5. NO NEW ESTIMATE (expected; unchanged).
EVALUATOR'S PATH TO 6 (verbatim substance): items 2 + 3 + a typed
dyadic-sufficiency (or literal uniformity) — WITHOUT needing a new
analytic estimate.  Above 6.5: a nontrivial witness or a new
obstruction.  B-1''' budget: 3 attempts; no delivered claims.

## AMENDMENT 4 (2026-07-13, own commit, pre-B-1'''' — external verdict
5.90/10 on B-1''': no artificial instantiation found; the frontier is
now LACUNARITY + OBSERVABLE-SUPPORT TRANSPORT + INTEGRATION)

VERDICT RECORDED: **5.90/10** (from 5.75).  Delivered per the
evaluator: canonical family without choice (exact dist identities),
nontrivial metric transport (factor 3 general, exact 2 canonical,
lower direction honestly open), Wilson probability CLOSED, scale-
corrected indexing, literal gate + cofinality with the converse
honestly open.  AUDIT NOTE ACCEPTED: the committed transcript is the
PRE-REBASE checkpoint (2050 invocations over b63b1861); the pinned
tree 23c36159 carries 2059 after the concurrent lane merged - actas
must distinguish measured-checkpoint vs merged-tree counts; and ONE
concatenated '#print axioms' line (merge residue) - FIXED in this
amendment's commit.

THE BLOCKERS OF 6 (B-1'''' spec, the evaluator's prescription):
1. LACUNARITY (the main blocker): the fidelity gate controls only
   r = 2^n*u with finite u-window - a finite union of dyadic
   subsequences with r/N FIXED (separations growing with volume),
   not all large separations and not fixed physical separation as
   N -> infinity (the thermodynamic form).  Need: a mechanism from
   the subsequence to ALL separations (monotonicity/interpolation/
   covering argument) OR the thermodynamic formulation (fixed t,
   N -> infinity).
2. OBSERVABLE-SUPPORT TRANSPORT: the transported observable after k
   steps is a 2^k-sized Wilson loop (each coarse edge = product of
   two fine edges), NOT the unit plaquette at a doubled anchor;
   need blockPlaquette / transported-loop support objects and the
   metric theorem for THEIR separations - anchor-point transport is
   proved, support transport is not.
3. INTEGRATION: one gate combining canonical/scaled objects (the
   fidelity corrections) WITH literal uniformity over all M0 -
   exists C gap, forall N, forall t, in the canonical scaled
   objects; currently fidelity-but-dyadic vs literal-but-old-objects.
4. All-pairs/translation-invariance still open (supAbsCorrelator
   not in the final gate); 5. no new estimate/obstruction
   (unchanged; B-2 territory).
Budget 3 attempts; no delivered claims; transcripts must state
their exact measured tree.

## AMENDMENT 5 (2026-07-13, own commit, pre-B-1^5 — external verdict
5.95/10 on B-1'''': no artificial instantiation; the main blocker is
now CIRCULARITY OF THE n=0 LAYER)

VERDICT RECORDED: **5.95/10** (from 5.90).  Delivered per the
evaluator: the integrated literal gate (correct quantifier order,
fidelity objects, no separate abstract gate), the ONE-STEP support
transport 2*tau - 3 over full pullback supports (called "the main
mathematical contribution of the checkpoint"), the honest covering
refutations, and the correctly-formulated conditional interpolation.
Tree-count discipline: 2097 = measured pre-rebase checkpoint, 2099 =
final dbd7dcb6 tree (2096 distinct, 3 dups, zero concatenations -
hygiene repair CONFIRMED by the evaluator).

THE ACCEPTED BLOCKERS (B-1^5 spec):
1. CIRCULARITY: allSeparations_of_literalFidelityGate consumes the
   n = 0 layer (M0 := N, u := t), where the tower performs NO
   blocking, scaled remainders clamp to zero, and the IR clause IS
   the sought forall-N-forall-t bound - the literal gate contains
   the result as a depth-zero hypothesis.  Valid implication,
   acknowledged in-docstring, but NOT a de-lacunarization mechanism
   and NOT a reduction of the open frontier.
2. CanonicalDoublingDomination remains open analytic input; it can
   even FAIL where Cov(s) = 0 but Cov(t) != 0 - not derivable from
   the dyadic bound by arithmetic; substantive step still
   conditional; t < 2^n untreated.
3. k-step support metric theorem missing (definition only).
4. No witnesses of any gate (expected; restated).

EVALUATOR'S PATH TO 6 (either suffices):
(A) prove CanonicalDoublingDomination - or a more natural
    substitute - for the Wilson data from REAL correlator
    properties; or
(B) reformulate the gate so the n = 0 layer does NOT presuppose the
    forall-t bound (all separations derived from POSITIVE scales)
    + the k-step transported-support metric theorem.
A new estimate or nontrivial obstruction lands clearly above 6.
B-1^5 budget: 3 attempts; no delivered claims; exact-tree
transcripts.

### Amendment 5 — VERDICT RULES FOR B-1^5 (evaluator-fixed,
registered pre-artifact; relayed verbatim to the in-flight desk)

1. NON-CIRCULARITY CHECKED IN THE TYPE: clauses mentioning
   towerMeasure do not suffice; `1 <= k_terminal` must be DERIVABLE
   in every consumed instance - nsc, truncated multiplication, or
   clamps must not silently allow k = 0.
2. The k-step metric counts as delivered ONLY if it controls the
   effective supports appearing in the TERMINAL correlator, with
   explicit slack preserving POSITIVE growth in k (non-vacuous on
   the stated window - the positivity side condition must be
   proved).
3. The domination-obstruction theorem counts as useful mathematical
   content iff it formalizes: a zero followed by a nonzero value
   excludes EVERY finite K.
4. The restricted substitute counts as a CONDITIONAL INTERFACE
   while its Wilson satisfiability stays open - stated plainly.
Frozen score pending the artifact: 5.95/10; the 6 barrier uncrossed.

### Amendment 5 — PRECISION ON RULE 1 (evaluator, pre-artifact,
relayed to the desk): a separate proof of 1 <= k_terminal will NOT
suffice - the inequality must be connected to the EXACT index used
in towerMeasure, the scaled canonical correlators, and the
consumer's telescoping.  If the type lets the terminal index exceed
the available depth and clamp back to the scale-zero measure or a
stationary stage, non-circularity does NOT count as closed: both
1 <= k AND k <= n must be typed and connected to the consumed
objects (no reachable clamp in any consumed instance).

### Amendment 5 — SECOND PRECISION ON RULE 1 (evaluator, pre-artifact,
relayed): a range lemma alone will not suffice - the gate's IR
clause and the physical reconstruction must consume the bounded
index DEFINITIONALLY or via a PROVED EQUALITY (the same index
expression in the IR clause, the tower objects, and the consumed
telescoping; no later substitution of a different nsc), checkable
by inspection of the types plus one connection theorem.

### Amendment 5 — DEFINITIVE kTerm CONSTRUCTION SPEC (evaluator,
pre-artifact, relayed verbatim; supersedes ambiguity in the earlier
rule notes): a SINGLE terminal index kTerm n with typed range
1 <= kTerm n <= n per consumed instance; the IR clause evaluates
EXACTLY towerMeasure ... (kTerm n) and its terminal correlator; the
telescoping ENDS exactly at that kTerm n (definitional reduction or
ONE proved equality); FORBIDDEN: later nsc, index rewrites, or
clamp-reachable indices; the consumer makes the five-step chain
visible (typed index / range / IR-terminal identity / physical
reconstruction through it / complete absence of the k = 0 layer);
k-step support metric FOR THE TERMINAL CORRELATOR's effective
supports with explicit slack + a PROVED strict-positivity theorem
on the window; the domination obstruction literally: Cov s = 0 and
Cov t != 0 => no K : R satisfies the domination.  No "delivered"/
"superado" anywhere; artifact + exact types + self-attack for
external verdict.

### Amendment 5 — THIRD PRECISION ON kTerm (evaluator, pre-artifact,
relayed): kTerm must not be a mere existential parameter with
bounds - its definition or data must DETERMINE the IR term actually
appearing in the reconstruction; a bridging equality reintroducing
equivalent freedom will not count.  Preferred: kTerm as a FIXED
definition pinning the consumed towerMeasure index syntactically,
with any single allowed equality connecting two occurrences of the
SAME defined term.

## AMENDMENT 6 (2026-07-13, own commit, pre-B-1^6 — external verdict
5.98/10 on B-1^5: non-circularity CLOSED per the definitive spec;
the blocker is now THE DECAY VARIABLE)

VERDICT RECORDED: **5.98/10** (from 5.95).  CLOSED per the evaluator:
kTerm determines the IR term (no existential, no free rewrite, no
clamp); the five-step chain visible; the domination obstruction
correctly literal.  Count discipline: 2109 = measured checkpoint,
2117 = final tree of 83aeef19 (2114 distinct, 3 dups, zero
concatenations).

THE ACCEPTED BLOCKERS (B-1^6 spec):
1. THE EXPONENT IS AT THE WRONG SCALE: the consumer concludes
   |C(2^n u)| <= C e^{-gap*u} - decay in the RENORMALIZED coordinate
   u, i.e. a fine-lattice gap gap/2^n that vanishes as n grows.  TO
   CROSS 6: keep kTerm >= 1 non-circularity AND conclude
   |C(2^n u)| <= C e^{-m * 2^n * u} with m > 0 independent of n -
   i.e. the gate's IR/UV clauses must demand decay in the PHYSICAL
   variable 2^n*u (the B-1'''' fidelity exponent shape) under the
   kTerm-fixed indexing.
2. K-STEP SUPPORT METRIC still required (vie-B second half), with
   the CORRECTED recursion: r_{k+1} <= 2 r_k + 2, r_0 = 0 gives
   r_k <= 2^{k+1} - 2 (the Addendum-496 slack quote 2^{k+2} was
   wrong - the evaluator's correction is adopted); separation
   target: >= 2^{k+1}*tau - 2*(2^{k+1} - 2) - slack with a PROVED
   strict-positivity window.
3. De-lacunarization from positive scales remains open (odd
   distances unreachable at n >= 1); an interpolation property or a
   different covering formulation is still needed - named, not
   faked.
4. A GENUINE Wilson obstruction (not conditional on a zero/nonzero
   pattern) would independently justify crossing 6.
B-1^6 budget: 3 attempts; no delivered claims; exact-tree
transcripts with the measured-vs-final distinction stated.

### Amendment 6 — VERDICT PRECISIONS FOR B-1^6 (evaluator,
pre-artifact, relayed verbatim to the desk):
1. The physical cast ((2 ^ n * u : N) : R) must appear LITERALLY in
   the exponent of BOTH the gate clauses and the consumer's
   conclusion; a u-bound plus narrative reinterpretation does not
   count.
2. The k-step metric counts only if the theorem applies to the
   support generating EXACTLY the terminal correlator at
   kTerm n = n (tied to the objects the IR clause consumes, not a
   free-floating generic support), with positivity a CONCRETE
   strict inequality after substituting k = n, on a window in
   (tau, M0) only - satisfiable independently of n.
Frozen: 5.98/10, pending the B-1^6 artifact or kill.

### Amendment 6 — FOURTH PRECISION (evaluator, pre-artifact,
relayed): the physical exponent must not live only in an auxiliary
definition - it must survive, without simplification or rewriting
toward u, in the PUBLIC type of PhysicalTerminalScaleWilsonGate and
of the final consumer (inline cast in the Prop and the conclusion).

## AMENDMENT 7 (2026-07-13, own commit, pre-B-1^7 — external verdict
5.99/10 on B-1^6: the physical exponent CLOSED, the multiscale
metric SUBSTANTIVE; one centesima from 6)

VERDICT RECORDED: **5.99/10** (from 5.98).  CLOSED per the
evaluator: the physical-variable decay blocker (cast literal in
public types, gap = min eps c0 independent of depth, telescoping at
the same kTerm, no reinterpretation); the k-step geometric
induction (real theorem, ZMod potential, one-step recovered as a
special case); the terminal instantiation at k = kTerm n = n with
rfl identification (terminalIR_is_canonical_pair_correlator) and
strict positivity 0 < 2^{kTerm n}(2u) - (2^{kTerm n}+1) for n >= 1,
u >= 1, with strict growth in depth.  Count discipline: 2149 =
measured checkpoint, 2158 = final tree of 25d4356e (2155 distinct,
3 dups, zero concatenations).

THE ONE MISSING CONNECTION (B-1^7 spec; the evaluator: "no redesign
of the gate, the exponent, or the metric is needed"): the module
proves (i) the IR object is a two-plaquette correlator under the
blocked measure and (ii) kStepBlockSupport has the right geometry -
but NOT the OPERATIONAL SUPPORT theorem composing them:
1. `kStepBlockObservable_congr` (inductive): if A = B on
   kStepBlockSupport(P, k) then
   f(plaquetteHolonomy(iteratedBlockMap A) P)
     = f(plaquetteHolonomy(iteratedBlockMap B) P) -
   the composed k-step pullback locality;
2. the INTEGRATION IDENTITY connecting that composed pullback with
   the correlator under towerMeasure (the k-fold pushforward):
   the terminal correlator IS the integral of the composed-pullback
   observable against the BASE measure, so the certified geometry
   of kStepBlockSupport is certified geometry OF THE OBSERVABLE the
   IR clause consumes.
NOT a gameability issue (kTerm fixed, n = 0 excluded, uniform
physical gap, support not choosable): a missing formal connection.
B-1^7 budget: 3 attempts; no delivered claims; exact-tree
transcripts with measured-vs-final distinction.

### Amendment 7 — THREE VERDICT CHECKS (evaluator, pre-artifact,
relayed): (1) towerMeasure_eq_map_iterated and
kStepBlockObservable_congr consume THE SAME composed-map term (one
iteratedBlockMap definition, not parallel iterations connected in
prose); (2) the integration identity transports ALL THREE terms of
the truncated correlator (product integral + both singles) in the
full truncatedPlaquetteCorrelatorOfMeasure shape; (3)
terminal_support_certified specializes to kTerm n = n, the exact
canonical IR pair, and the initial Wilson measure - no free
bridging hypothesis.  No further spec rounds; artifact or kill.

## AMENDMENT 8 (2026-07-13, own commit — external verdict 6.02/10 on
B-1^7: THE 6 BARRIER IS CROSSED, narrowly)

VERDICT RECORDED: **6.02/10** (from 5.99).  The evaluator: the three
pre-registered checks PASS (one composed map consumed everywhere;
all three truncated-correlator terms transported; the capstone fully
specialized with no bridging hypothesis, its conclusion jointly
carrying the integral identity, both observable localities, the
operational-support separation, and strict positivity); the support
identification is REAL (recursion-direction commutation + the
quantified terminal bridge over predicate families, instantiated at
the full metric property); "the 5.99 objection is closed - the
pullback observable provably depends on the set the metric applies
to."  Counts: 2184 = measured AND final (2181 distinct, 3 historical
dups, zero concatenations).

WHY ONLY 6.02 (accepted): the cross is FORMAL-STRUCTURAL, not
analytic.  Still unproved: a witness of
PhysicalTerminalScaleWilsonGate; the physical IR/UV bounds for the
Wilson measure; odd-separation interpolation; a genuine Wilson
obstruction; thermodynamic/continuum limits; operational locality of
the INTERMEDIATE UV remainders (k < n).  INTERFACE NOTE (accepted,
small): Measurable f should be packaged INTO the gate type so the
certification applies automatically to every admitted instance -
queued as a minor brick.

THE REGISTERED NEXT PHASE (the evaluator's closing rule adopted):
the next significant jump must NOT be another identification brick -
it requires (a) a nontrivial witness of the physical gate, (b) a new
Wilson estimate, or (c) a genuine Wilson obstruction.  That is
phase B-2 of this charter as originally registered (constructive
window vs obstruction, 3 attempts, 50-70% kill risk on record,
months-scale analytic content).  OWNER DECISION POINT: committing
the B-2 assault is a scale-of-effort choice the owner makes
explicitly; no fabrication before that order.

## AMENDMENT 9 (2026-07-13, own commit — OWNER CLOSURE ORDER: freeze
at 6.02, convert the B-1..B-1^7 arc into the C6 PAPER; B-2 = future
work or a second paper)

OWNER DECISION (verbatim substance): fabrication CLOSED; the score
freezes at 6.02; the arc is closable as a paper OF VERIFIED
FORMALIZATION AND CONCRETE RG ARCHITECTURE - not as a solution of
Yang-Mills, not as a mass-gap proof.  Publishable thesis: a
mechanized concrete RG chain for finite gauge measures in which the
effective measure is an explicit pushforward, the correlational
decomposition is telescopic, the terminal scale excludes
circularity, the conditional decay is stated in physical distance,
and the terminal observable's support is operationally certified
through the composed blocking map.

MANDATORY PROHIBITIONS (the paper may NOT say): mass gap proved;
PhysicalTerminalScaleWilsonGate has a witness; Wilson IR/UV bounds
obtained; all separations controlled; thermodynamic or continuum
limit exists; 6.02 as percentage proximity to Clay.

STRUCTURE (owner-fixed, 8 sections): 1 the specification problem
(why an abstract correlator decomposition is gameable); 2
adversarial countermodels (scalar relabeling, sink flow, clamp,
n=0 circularity) as "Naive interfaces and countermodels" - each as
initial definition + counterexample + typed repair; 3 the concrete
gauge RG (blockMap, towerMeasure, observable transport); 4 the
non-circular terminal gate (kTerm, telescoping, physical exponent);
5 support geometry (radius, separation, positivity); 6 operational
certification (iteratedBlockMap, composed pushforward, locality,
three-term integration); 7 the final conditional theorem; 8 the
open frontier (gate witness, Wilson estimates, odd separations,
limits).  REMOVE from the manuscript: the 4.60-6.02 scores, desk/
attempt/standby language, commit chronology (they stay in the
project record).  The countermodel history is presented as
ADVERSARIAL DESIGN OF FORMALIZED RG INTERFACES.  Title direction
(owner): "A Mechanized, Non-Circular Renormalization-Group
Interface for Wilson Lattice Gauge Correlators" - no "solution",
no "mass gap proved".

FREEZE: the paper freezes at d75d8952 or a strictly editorial later
commit.  Facts for the repro section: core 8409 jobs; oracle 2184
invocations (2181 distinct + 3 historical dups), zero sorryAx, zero
nonstandard; toolchain v4.29.0-rc6; Mathlib 0764272048...;
transcripts under docs/oracle-transcripts/.  Editorial assessment
on record: preprint reasonably closable now; competitive submission
needs narrative cleanup, module condensation, and a Lean-independent
mathematical exposition.  Then: five-role audit + release per the
C5 pattern (J-C6-PAPER).
