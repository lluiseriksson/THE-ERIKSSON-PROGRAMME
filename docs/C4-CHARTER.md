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
