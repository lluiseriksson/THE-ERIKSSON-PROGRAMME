# C5 CHARTER — "Optimal Amos-type barriers at real order: classifying the calibration constant"

Registered 2026-07-12, BEFORE the page.  Owner decision (evaluator
verdict on record): publish C4 clean (release blocked solely on the
two viXra ids), and open C5 as a clearly separate arc whose GOAL is
new mathematical content, not more formal hygiene — "the next
increment is turning the machinery into a factory of new theorems."
All C1-C4 lessons bind, PLUS the new rules: registering amendments
land in their OWN COMMIT strictly before the fabrication they
govern (C4 checklist MEDIUM); TeX/Lean content never through
non-raw Python string literals (C4 Amendment 8); annotated tags
only; post-push ids only.

## What the paper IS (honest scope, fixed now)

For the one-parameter family
  B_{nu,c}(x) = x / (nu + c + sqrt((nu+c)^2 + x^2)),
classify the constants c for which the upper bound holds uniformly:

  TARGET (classification):
    (forall nu >= 0, forall x > 0 :
       besselIReal (nu+1) x / besselIReal nu x < B_{nu,c}(x))
    <-> c <= 1/2.

C4 is the boundary case c = 1/2.  The registered mathematical
skeleton (derived at this desk BEFORE registration, to be verified
in fabrication):

1. GENERAL-c NULLCLINE IDENTITY (pure algebra): with a = nu+c,
   s = sqrt(a^2+x^2), B = x/(a+s) = (s-a)/x:
     Q(B_{nu,c}) = ((2c-1)/x) * B_{nu,c}
   where Q(y) = 1 - ((2nu+1)/x) y - y^2 is the C4 Riccati quadratic.
   Sign trichotomy in c: zero iff c = 1/2 (C4's calibration),
   positive iff c > 1/2, negative iff c < 1/2.
2. SUFFICIENCY (c <= 1/2): a |-> x/(a + sqrt(a^2+x^2)) is strictly
   decreasing in a, so B_{nu,c} >= B_{nu,1/2} for c <= 1/2, and
   C4's amosBoundReal_holds closes it.  LOW RISK.
3. NECESSITY (every c > 1/2 fails): requires a LOWER bound on rho
   sharp to FIRST order in 1/x at infinity.  Registered route: the
   RS16-type lower bound
     L_nu(x) = x / (nu + 1/2 + sqrt((nu+3/2)^2 + x^2))
   (large-x: L ~ 1 - (nu+1/2)/x + O(1/x^2), matching rho, while
   B_{nu,c} ~ 1 - (nu+c)/x — so L > B_{nu,c} for x large when
   c > 1/2).  Computed at this desk: Q(L) = (2nu+2) L / (x (a+s')),
   a = nu+1/2, s' = sqrt((nu+3/2)^2+x^2) — positive, explicit; the
   reversed barrier needs L' < Q(L) at touches (L' via the sqrt
   chain rule, machinery in place; the psi-trick does NOT transfer
   since L's calibration is not the nullcline: direct barrier).
4. COUNTEREXAMPLE ASSEMBLY: for each c > 1/2 an EXPLICIT witness
   x_0(c) (at nu = 0; one order suffices to kill uniformity) with
   L_0(x_0) > B_{0,c}(x_0) — an algebraic sqrt inequality in (c, x),
   target shape x_0(c) = K/(2c-1); no asymptotic limits in Lean,
   only the explicit instance.
5. CLASSIFICATION THEOREM: combine 2-4.

## THE REGISTERED HARD CORE (named now, before fabrication)

The lower bound's ZONE is a SECOND-ORDER fight: any valid lower
bound matches rho's first Taylor coefficient x/(2(nu+1)), so the
small-x comparison is decided at the next order — the exact reason
the old two-sided idea was deferred at C4 registration.  The zone
for L must compare two-term expansions with explicit q^2-tail
control (the C2/C4 product-form toolkit extended one order).  This
is where C5 lives or dies; it gets its own phase and budget.

## LITERATURE HONESTY CLAUSE (registered now)

HG13/HG24 prove in-family optimality results and RS16 prove
sharpness at both parameter ends: the classification c <= 1/2 (or
its correct orientation) MAY ALREADY BE KNOWN in equivalent form.
MANDATORY at paper phase: collate against HG13 Thms (G_{alpha,beta}
family), HG24, RS16 BEFORE any novelty sentence.  Registered
fallback wording: if the classification is classical, the paper's
contribution is "the first machine-checked classification,
uniform in real order, with certified counterexamples" — and the
absolute-importance expectation moderates accordingly.  No novelty
inflation; the evaluator's >7 estimate is CONDITIONAL on genuine
novelty or substantially sharper form.

## Phases, judges, budgets

- Phase 1 (LOW RISK): BFamily.lean — B_{nu,c} definition, general-c
  calibration Q(B_c) = ((2c-1)/x)B_c with sign trichotomy,
  monotonicity in c, SUFFICIENCY theorem (c <= 1/2) via C4.
  J-C5-1: green + oracle, sufficiency closed.
- Phase 2 (THE HARD CORE): the lower bound L — zone at second order
  (2a), reversed barrier (2b), besselLowerReal_holds.  J-C5-2.
- Phase 3: explicit counterexample family x_0(c) + THE
  CLASSIFICATION THEOREM.  J-C5-3.
- Phase 4: certified companion — pre-registered grid over (nu, x)
  for L, plus certified FALSIFICATION points for sample c > 1/2
  (points fixed at a later amendment IN ITS OWN COMMIT before the
  run, per the new rule).  J-C5-4.
- Phase 5: paper + five-role audit + release c5-v1.0 (annotated).
  J-C5-5.
Budgets: 3 attempts per phase; exhaustion -> diagnosis +
re-registration amendment in its own commit.

## Fallback ladder (declared now)

- If phase 2a (second-order zone) exhausts: honest partial =
  general-c calibration + sufficiency classification (c <= 1/2
  suffices, BY THEOREM) + certified numerical falsification of
  sample c > 1/2 (certified, not exact) — publishable as "the
  sufficiency half of the classification, with certified evidence
  for necessity"; necessity stays a named open target.
- If phase 2b (reversed barrier) exhausts with 2a green: the zone
  bound itself is a standalone real-order lower-tail theorem;
  same partial framing.
- No axioms, no vacuous weakening, no silent scope creep.

## AMENDMENT 1 (2026-07-12, own commit, BEFORE any fabrication —
external review of the registered target: THE PIVOT)

FINDING 1 (literature clause fired): the registered classification
is EQUIVALENT TO A KNOWN RESULT — RS16's family b_alpha with
lambda = mu + (alpha-1)/2 maps to ours by mu = nu+1, c = (alpha+1)/2
(so alpha <= 0 <-> c <= 1/2); RS16 prove alpha <= 0 are upper
bounds, alpha >= 1 lower bounds, intermediates NOT global bounds,
extremes best-in-family.  The classification is NOT novel; any
claim about it is "first machine-checked, uniform in real order,
constructive counterexamples" AT MOST.

FINDING 2 (the hard core dissolves): L_nu = x/(nu+1/2+
sqrt((nu+3/2)^2+x^2)) is a SHORT COROLLARY of C4, no new zone or
barrier: 1/rho_nu = 2(nu+1)/x + rho_{nu+1} (recurrence), C4 bounds
rho_{nu+1} < B_{nu+1,1/2}, inversion is decreasing on positives,
and the algebra collapses via x^2/(b+s') = s'-b (VERIFIED at this
desk: denominator 2(nu+1) + s' - b = nu + 1/2 + s').  Phase 2 is
REDEFINED accordingly: derive L by recurrence + inversion; the
second-order zone campaign is CANCELLED.

FINDING 3 (constructive witness): x_0(c) = 2/(2c-1) at nu = 0 as
the explicit counterexample for every c > 1/2 (algebraic sqrt
inequality L_0(x_0) > B_{0,c}(x_0); no limits in Lean).

NEW MAIN TARGET (registered now; this is where >7 lives): THE
CROSSING THEOREM for intermediate parameters 1/2 < c < 1 —
existence, UNIQUENESS, orientation, and quantitative localization
of the crossing point x_*(nu,c):
  rho_nu < B_{nu,c} on (0, x_*),  equality at x_*,
  rho_nu > B_{nu,c} on (x_*, oo),
plus  A_-(nu,c)/(2c-1) <= x_*(nu,c) <= A_+(nu,c)/(2c-1)  with
explicit A_±, and the c -> 1/2+ scale x_* ~ 1/(2c-1).
RS16 show intermediates are not global bounds; existence/
uniqueness/orientation/scale of the crossing AS A THEOREM is not
stated there — the novelty collation for THIS target is still
mandatory at paper phase.

DESK-DERIVED REFORMULATION (to verify in fabrication; found while
registering this amendment): by the general-c calibration
1/B_c - B_c = 2(nu+c)/x,
  rho_nu(x) < B_{nu,c}(x)  <->  psi_nu(x) > 2(nu+c)
with psi_nu = x(1/rho_nu - rho_nu) — C4's OWN barrier variable.
Hence the crossing theorem for ALL c in (1/2,1) SIMULTANEOUSLY is
equivalent to: psi_nu is STRICTLY DECREASING on (0,oo) with
psi_nu(0+) = 2nu+2 and psi_nu(oo) = 2nu+1 (endpoint values
paper-level; the Lean form needs only strict monotonicity plus the
constructive witnesses for level attainment).  Candidate route:
psi' < 0 from the C4 psi-derivative formula + the Riccati system —
equivalently x(rho_nu - rho_{nu+1}) strictly increasing (a
quantitative sharpening of the unit step).  THIS monotonicity is
the genuinely new analytic content; it gets the hard-core phase
and budget that the cancelled zone campaign vacates.

REVISED PHASES: 1 = BFamily + trichotomy + sufficiency (unchanged);
2 = L by recurrence-inversion + witness x_0(c) + the KNOWN-result
classification (all low risk); 3 = THE CROSSING THEOREM (psi
monotonicity route; 3 attempts; fallback: classification-only
paper with the crossing as named open target); 4 = certified
companion (grid points for L, falsification points for sample
c > 1/2, crossing-localization probes for x_*; protocol in own
commit before run); 5 = paper (novelty ONLY on the crossing
theorem, classification presented as machine-checked known result)
+ five roles + release c5-v1.0.

## AMENDMENT 2 (2026-07-12, own commit, pre-fabrication — external
verdict on the pivot: CORRECT, ">7 via defensible")

CORRECTION REGISTERED: the nu = 0 witness x_0(c) closes the UNIFORM
classification but NOT per-(nu,c) crossing existence.  The
parametrized crossing theorem needs TWO witnesses for EACH (nu,c),
both now registered explicitly (no asymptotics):
- SMALL SIDE: x_-(c) = sqrt(1-c), uniform in nu.  Route: C4's
  product bounds give rho < x/(2(nu+1)(1-q_{nu+1})); with
  sqrt(a^2+x^2) <= a + x^2/(2a), a = nu+c, the comparison reduces
  to 2(1-c) > (x^2/2)(1/(nu+c) + (nu+1)/(nu+2)); at x = x_-(c) the
  parenthesis is < 3 < 4 (1/(nu+c) < 2 for c > 1/2, ratio < 1),
  and q_{nu+1} = x_-^2/(4(nu+2)) < 1/16 auto-discharges the
  product-bound premise.
- LARGE SIDE: x_+(nu,c) = 2D/(2c-1), D = (nu+3/2)^2 - (nu+c)^2.
  Route: sqrt(b^2+x^2) - sqrt(a^2+x^2) = D/(sum of roots) < D/(2x),
  so L_nu(x_+) > B_{nu,c}(x_+), and rho > L closes the side.

TWO UNIQUENESS ROUTES REGISTERED (fabrication may use either; both
deliver the full crossing theorem):
- STRONG: psi_nu' < 0 globally (the Amendment-1 route).
- EXACT FALLBACK (transversality): at any zero of D_{nu,c} =
  rho - B_{nu,c},
    D'(crossing) = (B/x) * (2c-1 - (nu+c)/sqrt((nu+c)^2+x^2))
  (from Q(B_c) = ((2c-1)/x)B_c and B_c' = (a/(sx))B_c), which is
  POSITIVE iff x > x_dagger(nu,c) = (nu+c) sqrt(1/(2c-1)^2 - 1).
  Route: no crossing before x_dagger (local bound), every crossing
  after x_dagger is transversal with D' > 0, existence from the two
  witnesses => uniqueness + orientation.

LITERATURE COLLATION EXPANDED (mandatory, pre-novelty-sentence):
RS16 (intermediates "must cross" - but no explicit existence/
uniqueness/orientation/localization classification found in this
review); Segura 2021 double-ratio monotonicity (arXiv:2105.02524 -
close but not x(rho_nu - rho_{nu+1})); the 2026 Bernstein paper
(arXiv:2607.05538, W_nu(sqrt s) Bernstein via zeros of J_{nu+1} -
may imply parts via a stronger property; check the transfer).
Search terms fixed: normalized Turanian, adjacent-ratio difference,
double-ratio monotonicity, Bernstein/Stieltjes representations,
monotonicity of W_{nu-1} - W_nu.

REVISED SCORE LADDER ON RECORD (evaluator): phases 1-2 only:
6.90-7.00; + crossing uniqueness/orientation with per-(nu,c)
witnesses: 7.10-7.25; + global psi' < 0 (novelty confirmed):
7.25-7.45; + quantitative scale x_* ~ (nu+1)/(2c-1) with explicit
constants: 7.40-7.60.

## Known traps carried forward

The full C2-C4 bank (orphan rings after field_simp, rpow domain,
Gamma_add_one side goals, zero-suffix lemma names, cast-atom
push_cast, rw-at-hypothesis-not-goal for def-eta lemmas, explicit
root-module + Oracle imports with the +1 job-count witness,
le_total not le_or_lt, HasDerivAt.rpow_const value shape) plus:
sqrt-of-shifted-square calculus for L' (Real.sqrt HasDerivAt at
positive argument), and the second-order tail comparisons will
need explicit two-term partial sums (sum_le_tsum with range 2 as
in zero_lt, extended to range 3 if needed).
