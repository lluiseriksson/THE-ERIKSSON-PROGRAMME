# C4 CHARTER — "The Amos bound at real order: Gamma-series Bessel functions and the identification theorem"

Registered 2026-07-12, BEFORE the page.  Owner order (same date,
after C2+C3 published on viXra): open C4 = real-order extension,
the recommended candidate.  Part I remains temporarily postponed by
owner decision; C5 (two-sided/lower bound) is the registered
runner-up, explicitly deferred because any lower bound matches the
first Taylor coefficient of rho (rho = x/(2(nu+1)) + O(x^3)), making
its zone a SECOND-ORDER fight — C4's zone keeps the first-order gap.

All C1/C2/C3 lessons bind: day-one .txt transcripts, day-one dual
hashes, tag-after-rebase with ANNOTATED tags ONLY (git tag -a; the
lightweight/--follow-tags trap is twice-burned), commit ids from
POST-PUSH git log only (the orphan-twin ghost is twice-burned),
explicit staging (never add -A), same-lane self-citations from v1
(request the NEW viXra ids of C2/C3 from the owner at paper phase),
no hand-assembled predictions, audit enclosure methods not just
verdicts, tricotomy everywhere.

## What the paper IS (honest scope, fixed now)

Formalize, in the pinned central core, the Amos bound at REAL order
nu >= 0 over the Gamma-series definition:

  besselIReal (nu x : Real) := tsum k,
    (x/2)^(2*k+nu) / (k! * Real.Gamma (nu+k+1))     [rpow; x > 0]

  amosBoundReal_holds : forall (nu : Real), 0 <= nu -> 0 < x ->
    AmosBound nu x (besselIReal (nu+1) x / besselIReal nu x)

plus THE IDENTIFICATION THEOREM (the second half of C3's declared
scope limit, killed by theorem):

  besselIReal_natCast : forall (n : Nat) (x : Real), 0 < x ->
    besselIReal (n : Real) x = besselI n x

via rpow_natCast + Real.Gamma_nat_eq_factorial (both verified
present at the pin, 2026-07-12, before this registration; likewise
Real.Gamma_add_one, Real.Gamma_pos_of_pos, hasDerivAt_rpow_const,
rpow_add).  Consumers generalized to real order: the unit step and
the deriv-form log-derivative monotonicity.  The phi-step stays
integer-indexed (its sequence is integer by construction; already
unconditional via C3) — stated, not hidden.  C3's amosBound_holds
must be RECOVERED as a corollary through the identification (sanity
lock).  amosRHS / AmosBound / amos_calibration are ALREADY
real-parameter in Core.lean (verified 2026-07-12): the nullcline
side of the machine carries over by restatement, not new proof.

Scope limits stated in the paper from v1: nu >= 0 (the Amos74
range); x > 0; still NO identification with any external
special-functions library object (none exists at the pin to
identify with); the surface-track conditional does NOT change class
through this paper either.

## Proof design (registered before fabrication)

Phase 1 — INTERFACE (module AmosClosure/BesselRealInterface.lean):
  term def via rpow; exact term-ratio identity
  t_{nu,k+1} = t_{nu,k} * (x/2)^2 / ((k+1)(nu+k+1))
  [Gamma_add_one at s = nu+k+1 >= 1 > 0; rpow_add needs x/2 > 0];
  summability by comparison with geometric ratio
  q_nu = (x/2)^2/(nu+1) [same (k+1)(nu+k+1) >= nu+1 argument as C3];
  positivity termwise [rpow_pos_of_pos, Gamma_pos_of_pos,
  factorial pos]; recurrence
  besselIReal nu x = besselIReal (nu+2) x
    + (2(nu+1)/x) * besselIReal (nu+1) x   [termwise, index shift];
  IDENTIFICATION besselIReal (n:Real) x = besselI n x [termwise:
  rpow_natCast exponent (2k+n : Nat cast), Gamma_nat_eq_factorial].

Phase 2 — DERIVATIVE LAYER: termwise HasDerivAt
  [hasDerivAt_rpow_const, branch x != 0 on the interval]; dominated
  derivatives on Ioo (x/2) (3x/2) SUBSET (0,inf) — the C2.2 ball
  |y| < x+1 does NOT transfer (rpow needs positive base): the
  interval adaptation is the REGISTERED RISK ITEM of this arc;
  hasDerivAt_tsum_of_isPreconnected on the interval; identity
  I_nu' = I_{nu+1} + (nu/x) I_nu.

Phase 3a — RICCATI + NULLCLINE: restate riccatiQ/amosRHS_pos/
  amosRHS_calibration/riccatiQ_amosRHS/riccatiQ_pos_of_lt at real
  nu >= 0 (same algebra; a = nu+1/2 > 0); Riccati equation for
  rhoReal from phase 2 + recurrence via quotient rule.

Phase 3b — ZONE: mirror of C3 zone on (0, 1/4], uniform in
  nu >= 0: 2(nu+1) q_{nu+1} = (nu+1)x^2/(2(nu+2)) <= x^2/2
  [(nu+1)/(nu+2) <= 1], coefficient chain
  2nu+1+x^2 <= 2(nu+1)(1-q_{nu+1}), decisive strict inequality
  (2nu+1+x^2) I_{nu+1} < x I_nu, psi conversion INCLUDING the
  two-line step displayed in C3 v1.3 (I_{nu+1} <= x I_nu etc.).

Phase 3c — BARRIER: mirror of C3 sInf first-crossing in
  psiReal = x (1/rhoReal - rhoReal); touch forces rho' = 0;
  psi'(c) = (2nu+1)/c > 0 [needs nu >= 0 only through 2nu+1 > 0];
  antitone conversion identical.

Then amosBoundReal_holds; real-order consumers; C3 recovery
corollary via the identification.

## Pre-registered judges

- J-C4-1 INTERFACE: phase-1 module green + oracle-clean, INCLUDING
  the identification theorem.  Non-vacuity witness: the
  identification instantiated at n = 0 and n = 1 (ties to the
  already-witnessed C3 layer; no separate rational witness needed —
  stated as such, not silently).
- J-C4-2 DERIVATIVE: real-order derivative identity as HasDerivAt,
  oracle-clean, on the registered interval domination.
- J-C4-3 THE THEOREM: amosBoundReal_holds green + oracle-clean;
  real-order unit step + deriv-form log-derivative monotonicity as
  corollaries; amosBound_holds (C3) RE-DERIVED as corollary via the
  identification — if the recovery fails, the identification is
  wrong somewhere: full stop + autopsy.
- J-C4-4 CROSS-CHECK: the committed C2 1206-point transcript
  re-read; its nu-coverage stated EXACTLY (if the grid is
  integer-only in nu, the paper says the numerical cross-check
  covers the integer slice only — no silent stretching).  Any new
  grid = new registered run with its own charter amendment.
- J-C4-5 PAPER + AUDIT + RELEASE: tex+pdf same commit; tricotomy;
  scope section per above; five-role audit (math referee, hostile
  editor, checklist/formal-hygiene, formal+repro on release tree,
  external-tool desk); tags c4-v1.0(.x) ANNOTATED,
  tag-after-rebase, post-push ids only, tag-scoped manuscript
  hashes from v1.

## Attempt budgets and fallback (declared now)

THREE registered attempts per phase (1, 2, 3a, 3b, 3c); exhaustion
=> diagnosis + re-registration by amendment (the C3 Amendment-1
protocol).  Fallbacks, in order of retreat:
- If phase 3 (any sub-phase) dies: honest partial delivery =
  interface + identification + derivative layer as a standalone
  paper ("the real-order Bessel interface, with the integer-order
  identification as a theorem"); amosBoundReal_holds stays the
  named open target.  This partial ALONE already converts C3's
  integer-identification caveat into a theorem — publishable.
- If phase 2 dies: interface + identification alone (same framing,
  smaller); phase-2 residue documented.
- No axioms, no vacuous weakening, no silent scope creep, ever.

## AMENDMENT 1 (2026-07-12, mid-course external audit of phase 1 —
verdict: phase 1 authentic, J-C4-1 substantially met; artifact
5.80/10 on the absolute scale, 6.65 potential at full closure)

ADJUSTMENT 1 — METHOD DEVIATION RECORDED (audit-mandated): the
charter pre-registered summability "by comparison with geometric
ratio q_nu"; the fabricated proof uses a DIFFERENT route — the
Gamma-monotone exponential-series majorant
  t_{nu,k} <= ((x/2)^nu / Gamma(nu+1)) * ((x/2)^2)^k / k!
obtained from Gamma(nu+1) <= Gamma(nu+k+1) (induction on the
functional equation), then Real.summable_pow_div_factorial.
Conclusion and scope UNCHANGED; the fabricated route is cleaner
(mirrors C2's besselTerm_le pattern).  Recorded per regime: a real
charter-vs-fabrication difference, not a defect.

ADJUSTMENT 2 — WITNESSES NAMED (audit-mandated): the n = 0, 1
anchors were `example`s (compiled but unnamed, not in the oracle).
Converted to `besselIReal_zero_eq` / `besselIReal_one_eq` and
registered: oracle 44 entries.  Literal compliance restored.

PHASE-2 DESIGN REFINEMENT (adopted from the audit, REGISTERED
before phase-2 fabrication): the naive sup-majorant on the
derivative series is FALSE at k = 0 for 0 <= nu < 1 — the termwise
derivative d/dy (y/2)^(nu+2k) = ((nu+2k)/2)(y/2)^(nu+2k-1) has
NEGATIVE exponent nu-1 there (decreasing in y; supremum at the LEFT
endpoint).  Registered structure:
  (i) treat k = 0 separately (its derivative bound evaluated at the
      left endpoint x/2);
  (ii) for k >= 1 use nu+2k-1 >= 1 (increasing; right endpoint);
  (iii) work on the CLOSED interval [x/2, 3x/2] subset (0, inf);
  (iv) dominate by C(nu,x) * (nu+2k) * A^k / k! with
       A = (3x/4)^2; prove summability of sum A^k/k! and
       sum k*A^k/k! SEPARATELY (the second via k/k! = 1/(k-1)!).

PHASE-3 LOCKS (adopted from the audit): the recovery corollary
amosBound_holds_recovered must be SHORT — target shape
  rw [<- besselIReal_natCast, <- besselIReal_natCast];
  exact amosBoundReal_holds ...
If it needs long rewrite chains or new hypotheses, that is evidence
of divergence between the objects: full stop + autopsy, not
patching.  ADDITIONALLY a genuinely non-integer named witness is
REQUIRED: amosBoundReal_half_order (nu = 1/2 instance; no closed
sinh form needed, just the named endpoint outside Nat.cast).

J-C4-4 GRID PRE-REGISTERED NOW (points fixed before any run): new
certified interval-arithmetic run (same arb methodology and
committed-transcript rules as the C2 companion) on
  nu in {0, 1/10, 1/2, 9/10, 1, 3/2, 2, pi, 10, 100}
  x  in {1/8, 1/4, 1, 2, 5, 50, 300}
(70 points; strict-inequality certification of eq. Amos at real
order).  Detection targets, stated now: Gamma normalization errors,
nu -> nu+1 shift errors, inverted barrier sign, behavior near
nu = 0, precision loss at large nu, x.  The grid PROVES NOTHING
about all real nu; it is an independent cross-check and will be
labelled exactly that.  The integer-only C2 grid alone is
INSUFFICIENT for C4's paper (audit concurrence with the charter).

PAPER GATE (audit-adopted): not one page of the C4 paper before
phase 2 closes — the derivative layer decides whether C4 is the
full theorem or an interface paper (fallback ladder unchanged).

## AMENDMENT 2 (2026-07-12, pass verdict on the audit-application
round: J-C4-1 literal compliance CONFIRMED by independent re-check
of a9f61179; phase-2 implementation refinement REGISTERED before
fabrication)

K>=1 FACTORING (auditor's improvement, replaces Amendment 1 (iv)
detail): write nu+2k-1 = (nu+1) + 2(k-1), so
  (y/2)^(nu+2k-1) = (y/2)^(nu+1) * ((y/2)^2)^(k-1)
- NEVER reintroducing the possibly-negative exponent nu-1 at k>=1.
On [x/2, 3x/2]: (y/2)^(nu+1) <= (3x/4)^(nu+1) (base-monotone since
nu+1 >= 1) and ((y/2)^2)^(k-1) <= A^(k-1), A = (3x/4)^2.  Majorant
sum over k>=1: (nu+2k)A^(k-1)/k! = nu*A^(k-1)/k! + 2k*A^(k-1)/k!;
k/k! = 1/(k-1)! collapses the second, 1/k! <= 1/(k-1)! dominates
the first; both are multiples of sum_j A^j/j! after j = k-1.  No
A^{-1} anywhere.

K=0 SUBCASES (auditor): nu = 0 -> the derivative term is EXACTLY
zero (factor nu); 0 < nu < 1 -> negative exponent, sup at LEFT
endpoint; nu >= 1 -> increasing (kept inside the separate k=0 case
for design simplicity).  Single uniform k=0 bound admissible:
(y/2)^(nu-1) <= (x/4)^(nu-1) + (3x/4)^(nu-1) (sum dominates the
endpoint max in both monotonicity regimes).

REGISTERED LEMMA SEQUENCE (phase 2): besselRealTerm_hasDerivAt ->
besselRealTerm_deriv_zero_bound -> besselRealTerm_deriv_succ_bound
-> summable_besselRealDerivMajorant -> besselIReal_hasDerivAt ->
besselIReal_deriv_identity with final identity
  I_nu'(x) = I_{nu+1}(x) + (nu/x) I_nu(x).
Internal consistency test (NOT a judge): specializing nu = n must
recover the integer derivative identity through besselIReal_natCast.

GRID EXECUTION PRECONDITIONS (protocol lock, audit-mandated): the
70-point J-C4-4 grid must NOT run until a registered protocol fixes
(i) the exact formula evaluated, (ii) initial precision,
(iii) precision-escalation policy, (iv) exact PASS/FAIL/UNDECIDED
criteria, (v) the quotient evaluation method - scaled ratio or
certified recurrence/continued-fraction, NEVER two giant I_nu
values divided naively (at x = 300 both blow up while the ratio is
moderate), (vi) certified representation of pi.  These go in a
J-C4-4 protocol registration before any run; transcripts committed
per house rules.

## AMENDMENT 3 (2026-07-12, phase-2 verdict + phase-3 registration)

PHASE-2 VERDICT RECORDED: external desk confirmed the 346353b2
package by independent re-check (53-entry oracle, 8168 jobs,
elaboration of BesselRealDeriv verified); J-C4-2 CLOSED; C4 at
6.10/10 absolute (up from 5.80; intermediate-artifact 8.6),
potential 6.65-6.80.  "The hard analytic layer is no longer a
promise."

DOCUMENTARY ALIGNMENT (audit finding, one sentence, no code
change): the implementation differentiates over `Ioo (x/2) (3x/2)`
and uses the closed-interval endpoints only to build the uniform
majorant.  Charter and fabrication are thereby fully aligned.

PHASE-3 REGISTRATION (names and shapes fixed BEFORE fabrication,
per the audit's design):
- 3a RICCATI REAL: besselRatioReal := besselIReal (nu+1) x /
  besselIReal nu x; besselPsiReal := x*(1/rho - rho); lemmas IN
  ORDER: besselRatioReal_pos, besselRatioReal_hasDerivAt (the
  equation rho' = 1 - rho^2 - ((2nu+1)/x) rho from phase-1
  recurrence + phase-2 derivative, quotient rule),
  besselPsiReal_hasDerivAt, riccati_zero_of_real_touch; plus the
  real restatements riccatiQReal / amosRHS facts (amosRHS already
  real-parameter; calibration algebra order-agnostic).
- 3b ZONE REAL (the one place implementation-new mathematics can
  still appear): besselRealTerm_le_geometric, besselIReal_mul_le,
  besselRealTerm_zero_lt_besselIReal, besselRealTerm_zero_succ,
  besselPsiReal_zone; geometric ratio q_{nu+1} = (x/2)^2/(nu+2);
  UNIFORMITY exactly from (nu+1)/(nu+2) <= 1, never from
  discretizing nu; decisive chain ends in
  (2nu+1+x^2) I_{nu+1}(x) < x I_nu(x) on (0, 1/4], then
  2nu+1 < psi_nu(x).  STRICTNESS WATCH: the sum bound may be
  non-strict; the positive tail must supply the strict link.
- 3c BARRIER REAL: port the C3 sInf architecture NEARLY LITERALLY
  (closed set, csInf membership, exclude c = 1/4 by zone, exact
  touch, Q = 0, psi'(c) = (2nu+1)/c > 0, first-crossing
  contradiction); what Nat.cast_nonneg supplied now comes from
  0 <= nu; do NOT informally "simplify" the topology.
- LOCKS (unchanged, shapes fixed): amosBound_holds_recovered =
  two natCast rewrites + exact amosBoundReal_holds (minor cast
  normalization allowed, NO new mathematical chain);
  amosBoundReal_half_order at nu = 1/2 with rho = besselIReal (3/2)
  / besselIReal (1/2) (proves the endpoint lives outside Nat.cast).

## AMENDMENT 4 (2026-07-12, 3a verdict + 3b safe route registered)

3a VERDICT RECORDED: external desk confirmed b19b6bd3 (61-entry
oracle, 8169 jobs, RiccatiReal elaborated); J-C4-3a CLOSED; C4 at
6.25/10 absolute, artifact 8.75, potential 6.75-6.85.  No hidden
hypothesis, no trivializing redefinition, no extra axiom found.

3b SAFE ROUTE (audit-adopted, registered before fabrication):
- geometric domination FROM THE PHASE-1 RATIO IDENTITY
  besselRealTerm_succ (no Gamma/rpow redeployment), reduced to
  nu+1 <= (k+1)(nu+k+1); hypothesis x > 0 (not x >= 0 - rpow);
- product bound mirroring the integer consumer (tsum_le_tsum +
  geometric series);
- STRICTNESS exclusively from t_{nu,0} + t_{nu,1} <= I_nu with
  t_{nu,1} > 0; any strict inequality appearing BEFORE
  x t_{nu,0} < x I_nu in the chain is an audit flag;
- initial-term identity 2(nu+1) t_{nu+1,0} = x t_{nu,0} derived
  from the ALREADY-PROVED besselRealTerm_rec_zero (multiply by x) -
  Gamma/rpow do not reappear at all in 3b;
- TWO NAMED AUXILIARY LEMMAS (visibility of the uniformity
  mechanism, not automation): real_zone_ratio_uniform
  ((nu+1)/(nu+2) <= 1) and real_zone_coefficient_bound
  (2nu+1+x^2 <= 2(nu+1)(1-q_{nu+1}) for 0 < x <= 1/4);
- SHIFT RISK flagged: the domination lemma is at parameter nu, the
  zone consumes it at nu+1 (q_{nu+1} = (x/2)^2/(nu+2)); the
  (nu+1)+1 = nu+2 rewrite is the likely silent-error site.

## AMENDMENT 5 (2026-07-12, 3b verdict + 3c port adoption)

3b VERDICT RECORDED: external desk confirmed b7e241dd (68/68,
8170 jobs; "no strictness loss, no covert discretization of the
real parameter"); J-C4-3b CLOSED; C4 at 6.45/10, artifact 8.90,
potential 6.80-6.90.  The zone was the last site where real-order
could demand a new analytic idea.

3c ADOPTIONS (registered before fabrication): port besselPsi_gt
NEARLY LINE-BY-LINE (no redesign); THREE WATCHPOINTS: (i) the
touch-derivative positivity via explicit `0 < 2nu+1 := by linarith`
+ div_pos, NOT positivity on a fragile normalization; (ii) the
slope orientation ported with the existing div_pos_iff analysis, no
new automation; (iii) IsClosed S via
ContinuousOn.preimage_isClosed_of_isClosed on Icc, no gratuitous
global-continuity upgrade.  Recovery lock: cast-normalization
rewrites acceptable, a new analytic chain triggers the registered
autopsy.  Half-order witness consumes the general endpoint
directly.  Consumers: real unit step + real logDeriv increase ONLY;
NO artificial real phi-step (stays integer-indexed per charter).

## AMENDMENT 6 (2026-07-12, 3c verdict + J-C4-4 GRID PROTOCOL
REGISTERED + title caution)

3c VERDICT RECORDED: external desk confirmed 56ff479b (74/74
oracle, 8171 jobs, endpoint hypotheses exactly nu>=0 and x>0, both
locks in correct form, no project axioms); J-C4-3 CLOSED; C4 at
6.85/10 absolute, formal artifact 9.05 ("#1 or #2 by formal depth,
top 3 global, likely above C1 in pure analytic difficulty").
"The remaining work is independent certification, exposition and
provenance."

TITLE CAUTION (audit-mandated): until the PRIMARY SOURCE (Amos,
Math. Comp. 28 (1974) 239-251) is checked directly for the exact
formula, inequality orientation, nu-range, proof-vs-algorithm
status, and equation number, the paper title is
  "A machine-checked proof of an Amos-type bound for modified
   Bessel ratios at real order"
- switchable to "the Amos bound" ONLY after the primary-source
check.  The paper's attribution sentences carry the same caution.

J-C4-4 PROTOCOL (registered NOW, before any run; the six
Amendment-2 preconditions discharged):
(i) FORMULA CERTIFIED: the margin Delta(nu,x) = B_nu(x) - rho_nu(x)
    directly; PASS iff inf Delta > 0 (provably positive ball);
    FAIL iff sup Delta <= 0; UNDECIDED if the ball straddles 0.
    NEVER a midpoint verdict.
(ii) QUOTIENT METHOD: certified BACKWARD recurrence
    rho_alpha = x / (2(alpha+1) + x rho_{alpha+1})
    (decreasing in rho_{alpha+1} > 0; arb-ball propagation), NEVER
    forming I_nu at large x.  ANCHOR at alpha = nu + N with N
    minimal such that q_alpha = (x/2)^2/(alpha+1) <= 1/4, seeded by
    the PHASE-3b-STYLE two-sided bound
    rho_alpha in [ (x/(2(alpha+1)))(1-q_alpha),
                   (x/(2(alpha+1)))/(1-q_{alpha+1}) ]
    (from t_0 < I <= t_0/(1-q) at both orders + the zero_succ
    identity) - independent of the Amos theorem, valid at
    non-integer order, no giant values anywhere.
(iii) PRECISION: start 128 bits; on UNDECIDED double through 256,
    512, 1024, 2048, 4096; if still undecided PRINT UNDECIDED,
    never force a verdict.
(iv) pi: certified Arb ball (arb.pi()), never a pasted decimal.
(v) PER-ROW RECORD: nu, x, depth N, final precision, margin as
    mid +/- rad, verdict boolean.
(vi) INDEPENDENCE CONTROL: a second, ordinary high-precision pass
    (mpmath) labeled VERIFIED - NOT certified - to catch script or
    index-shift errors in the Arb harness itself.
Grid: the 70 pre-registered points (Amendment 1).  Transcript
committed day-one per house rules; provenance header (script
sha256, library versions, parameters).

PAPER STRUCTURE ADOPTED (audit's 10-section narrative): Gamma-series
+ convergence; identification; termwise differentiation; Riccati;
uniform real zone; barrier + the bound; consumers + C3 recovery;
certified companion; paper-Lean map + reproducibility; scope +
novelty ("first machine-checked formalization of this complete
chain in the repository and, absent a prior formalization,
possibly the first formalization of the result" - NOT a new
classical inequality).

## Known pin traps carried forward

The full C2/C3 bank (Summable.-namespaced tsum lemmas, zero-suffix
div lemmas, Pi.mul/id shapes from HasDerivAt.mul, field_simp needs
x != 0 as hypothesis, simpa 1/x normalization, convert+ring,
mul_lt_mul_of_pos_left, self_mem_nhdsWithin +
mem_nhdsWithin_of_mem_nhds(isOpen_Ioi.mem_nhds), IsClosed.csInf_mem,
hasDerivAt_iff_tendsto_slope, omega-normalized index rewrites)
PLUS the new rpow/Gamma class: rpow domain (positive base
everywhere, no |y| balls through 0), Gamma_add_one side goal
s != 0, rpow_add needs 0 < x, exponent arithmetic in Real not Nat
(no omega — linarith/ring on reals).
