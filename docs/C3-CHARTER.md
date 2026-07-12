# C3 CHARTER — "The Amos bound, formalized: a Riccati barrier proof over series-defined Bessel functions"

Registered 2026-07-12, BEFORE the page.  Owner order: open C3 after
circulating C2; Part I and PlaneTree postponed.  C3 is a NEW paper,
not a C2 revision (per the C2 acceptance verdict: the next arc is a
new major contribution).  All C1/C2 lessons bind (day-one .txt logs,
day-one dual hashes, tag-after-rebase, tag-scoped manuscript hashes,
no hand-assembled predictions, same-lane self-citations from v1,
audit enclosure METHODS not just verdicts).

## What the paper IS (honest scope, fixed now)

Formalize, in the pinned central core, the Amos upper bound itself
over the series-defined besselI:

  amosBound_holds : forall (n : Nat) {x : Real}, 0 < x ->
    AmosBound n x (besselI (n+1) x / besselI n x)

With it, EVERY consumer of the C2 lane becomes UNCONDITIONAL over
besselI: the unit step, the deriv-form log-derivative monotonicity,
and the phi-monotonicity step lose their last hypothesis.  (The
surface track's E' < 0 for beta <= 3.5 does NOT thereby become
unconditional - its phi-lemma consumes ratios of the CLASSICAL
I_nu, and the identification besselI = classical I_nu is outside
this arc; the paper will state this scope limit explicitly.)

## Proof design (registered before fabrication)

Everything reduces to existing C2 theorems plus one ODE-barrier
argument:

1. RICCATI (pure algebra from C2): with rho(x) = besselI (n+1) x /
   besselI n x, the quotient rule on besselI_hasDerivAt at orders
   n, n+1 plus the recurrence gives
     HasDerivAt rho (1 - (2n+1)/x * rho x - rho x ^ 2) x
   for x > 0.  [Uses: HasDerivAt.div, besselI_hasDerivAt,
   besselI_recurrence, besselI_pos.]
2. THE BOUND IS THE NULLCLINE: B(x) = amosRHS n x satisfies
   Q(B) = 0 where Q(y) = 1 - (2n+1)/x * y - y^2 - this is EXACTLY
   the calibration identity 1/B - B = (2n+1)/x already at the heart
   of amos_calibration.  Also 0 < B, B < 1-side facts, and
   Q(y) > 0 for 0 <= y < B (Q strictly decreasing in y >= 0).
3. B IS DIFFERENTIABLE WITH B' > 0 on x > 0: composition
   (Real.sqrt deriv); B' > 0 either by explicit computation or via
   the implicit form (B = positive root of y^2 + (2n+1)/x y - 1;
   as x increases the root increases).  Fallback within the arc:
   B' >= 0 suffices if the barrier uses strict Q > 0 just below B.
4. SMALL-x ZONE: for 0 < x <= 1/(2n+4):
     rho(x) <= (x/2)/(n+1) * exp((x/2)^2)   [series majorant +
       first-term lower bound, both C2 artifacts; exp form via
       1 - u <= exp(-u), i.e. Real.add_one_le_exp]
     B(x) >= x/(2n+1+x)                     [sqrt(a^2+x^2) <= a+x]
   and the elementary chain x + (2n+2)(x/2)^2/(1-(x/2)^2) < 1
   closes rho < B on the zone.
5. BARRIER: h = rho - B continuous on (0, oo) (from HasDerivAt),
   h < 0 on the small-x zone; if E = {x in (0, x1] : h >= 0} were
   nonempty with c = sInf E, then h(c) = 0 (continuity + zone), and
   h'(c) = Q(rho(c)) - B'(c) = Q(B(c)) - B'(c) = -B'(c) < 0, so h > 0
   on a left-neighborhood of c, contradicting c = sInf.  [Topology:
   sInf membership via IsClosed/continuity on the interval, the
   left-neighborhood lemma from the slope characterization of
   HasDerivAt with negative derivative.]

## Pre-registered judges

- J-C3-1 RICCATI: HasDerivAt rho (Q(rho x)) x proved, oracle-clean,
  as pure consequence of C2 theorems (no new analytic input).
- J-C3-2 THE THEOREM: amosBound_holds green + oracle-clean; the
  three unconditional consumer corollaries
  (besselI_unit_step_unconditional, besselI_logDeriv_lt_unconditional,
  besselI_phi_step_unconditional) stated and proved by direct
  application.
- J-C3-3 CROSS-CHECK: the C2 certified companion's 1206-point grid
  is re-read as an INDEPENDENT numerical witness of the now-proved
  theorem (no new run needed; the paper cites the existing committed
  transcript); any future grid extension is a new registered run.
- J-C3-4 PAPER: tex+pdf same commit; tricotomy; the scope limit
  (series-defined besselI, integer orders, x > 0; no identification
  with classical I_nu claimed); related work incl. Amos74/Segura11/
  HG13/RS16/HG24 and own preprints; reproducibility with
  theorem-artifact map, tag-scoped hashes from v1.
- J-C3-5 AUDIT: five roles as C2; release tags c3-v1.0(.x);
  tag-after-rebase sequence.

## Fallback (declared now)

The arc has THREE registered sub-attempts per Lean phase (Riccati /
zone / barrier).  If the BARRIER phase resists its three attempts,
the fallback is honest partial delivery: the Riccati equation and
the zone bound are standalone theorems (paper reframed as "the
Riccati structure of the Amos bound, formalized, with the barrier
step paper-level"), and amosBound_holds stays the named open target.
No axioms, no weakening, no silent scope creep.

## AMENDMENT 1 (2026-07-12, phase 2a attempt budget exhausted -
measured, diagnosed, and re-registered)

Phase 2a (zone) consumed its three registered attempts (run
transcripts 2-4 committed).  DIAGNOSIS OF THE RESIDUE: no
mathematical resistance - every zone inequality (geometric
domination induction, product-form geometric bound, strict two-term
lower bound, exact first-term identity, the 2n+1+x^2 coefficient
chain, the final psi assembly) elaborated; the surviving failures
are TWO mechanical items: (i) the pin's HasDerivAt.mul produces the
Pi.mul function-product (id * f) whose defeq to the lambda form
convert does not close - fix is a funext/simp[Pi.mul_apply] rewrite
of the function before convert (same CLASS as the C2.2 pow-shape
trap, now banked); (ii) one orphan tactic line after goals closed
in the zone assembly.  Attempt-1 catches along the way included a
REAL mathematical error in this desk's own draft (a q <= x^2/8
bound losing the n-dependence, caught before compilation and fixed
to the exact 2(n+1)q = (n+1)x^2/(2(n+2)) <= x^2/2 chain) - recorded
per prose-discipline.

RE-REGISTRATION: phase 2a' opens with a budget of TWO attempts
scoped strictly to the two mechanical residues (no statement
changes, no new mathematics).  If 2a' exhausts its budget, the
phase falls back per the charter (zone paper-level, Riccati
standalone).

## AMENDMENT 2 (2026-07-12, J-C3-5 audit registry - fabrication-side
desks, round 1)

Three independent desks audited manuscript v1.1 (dabef64c) against
the Lean sources at 538562dc, the committed transcripts, and the
external reviewer's 8-point checklist.

MATHEMATICAL REFEREE - verdict VERIFIED, zero mathematical
discrepancies: both theorem statements match the Lean exactly
(quantifiers, hypotheses, conclusion shape, deriv-form); EVERY
displayed identity re-derived correctly by hand (Riccati algebra,
Q(B)=0 via (s-a)(s+a)=x^2, factorization, geometric domination
with the (k+1)(n+k+1) >= n+1 step, the exact 2(n+1)q_{n+1} chain,
coefficient inequality, decisive chain incl. the unadvertised
h2/h3 auxiliary, psi-multiplication, touch, psi'(c), antitone
product); Lemma 4.1 prose matches AmosBarrier.lean step-for-step;
28 = 18+10 accounting exact vs the committed log; cross-refs and
scope clean.  Findings: D1 closing-step wording inverted the
inference direction (minor); D2 = HE-1 below; D3 three map rows
"exact" with only transitive oracle witness; D4 minimality interval
endpoint; D5 phi-step order sharpening; one stale mid-thought
comment at AmosBarrier.lean:127 (cosmetic).

HOSTILE EDITOR - two SEVERE (RELEASE-MANIFEST.md asserted in
present tense but nonexistent at v1.1; "all 28 module statements"
literally false, module has more named lemmas), three MEDIUM (tag
tense, comma splice, house jargon x5+), four LOW ("provably" vs
tricotomy, truncated self-citation subtitles, "top-level namespace"
imprecise, "consumer" unglossed).  VERIFIED CLEAN: novelty-claim
hygiene (no sentence claims the mathematics as new; all
first-formalization claims hedged), scope sentence twice verbatim,
tricotomy placement, every witnessed fact re-checked against
committed artifacts (commit ids, job counts, transcript tails,
grid figures, toolchain pins, C2 citation form).

CHECKLIST + FORMAL-HYGIENE AUDITOR - PASS on all six items: oracle
INDEPENDENTLY RE-RUN (exit 0, 28/28 conforming, LF-normalized
byte-identical to the committed log); sorry/admit/axiom grep zero;
all eight transcripts' labels match their content tails and job
counts (8164/8165/8166 chain coherent); charter pre-registration
and Amendment-1 ordering verified by git ancestry (77fe704c ->
19504635 -> 70499e22 [runs 2-4 + amendment, same commit] ->
c05dfc36 [2a'-1 FAIL, 2a'-2 GREEN] -> 538562dc); reviewer 8-point
checklist 8/8; command-sequence premises all hold (lake target,
toolchain, dual pin agreement, tectonic 0.15.0).

DISPOSITIONS (all applied in the release commit, manuscript v1.2):
D1/D4/D5 and HE-3..9 prose fixes; HE-1/D2 closed by committing
papers/c3-amos-proof/RELEASE-MANIFEST.md together with the
manuscript; HE-2/D3 closed by the STRONG route - Oracle.lean v2
registers the six supporting lemmas (direct witnesses for every
"exact" map row): 34 entries all clean, green rebuild run 9 (8166
jobs), log scripts/c3_oracle_output_v2.txt; the stale comment
removed.  Full mapping in papers/c3-amos-proof/CHANGELOG.md.

J-C3-4 closes at the release commit.  J-C3-5 sequencing per the C2
pattern: tag c3-v1.0 after these desks; formal+repro audit on the
RELEASE TREE + external-tool desk recorded post-tag in the manifest
addendum (fixes, if any, in post-tag commits; tags never move).
