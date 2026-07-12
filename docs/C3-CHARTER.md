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
