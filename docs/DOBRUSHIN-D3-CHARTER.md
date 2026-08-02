# D-3 CHARTER — the comparison estimate
# Registered 2026-08-01, BEFORE any fabrication of this rung.

Owner authorisation: explicit, in-session, to open the lane that carries the
chain from the resolvent bound to decay of correlations.  This is the obligation
the paper names as the only currently identified new analytic estimate.

## What D-3 must produce, stated so it can fail

The chain currently closes at
```
    envelope (D-2a)  ->  matrix + local window (D-2b/c)  ->  resolvent (D-1)
```
and stops.  D-3 must produce the missing implication
```
    |Cov_mu(f,g)|  <=  sum_{i,j}  delta_i(f) * D_ij * delta_j(g),
    D = sum_n C^n,
```
so that the resolvent bound of D-1 becomes exponential decay of connected
correlations at a rate free of the volume.

## THE LADDER, and what each rung is worth ALONE

* **D-3a — the oscillation seminorm.**  `deltaAt j f`, the oscillation of a real
  observable in the single coordinate `j`, over a FINITE configuration space.
  Basic algebra: nonnegativity, subadditivity, vanishing exactly when `f` does
  not depend on `j`.  **Worth alone: a definition and its lemmas.  No physics
  claim may be attached.**
* **D-3b — the single-site conditional operator.**  `E i f`, built from a
  single-site kernel `p i eta s` that is nonnegative, normalised, and local
  (depends on `eta` only off `i`).  Nothing probabilistic beyond finite sums.
* **D-3c — THE KEY LEMMA, and the rung that decides the campaign.**
  ```
      delta_i (E i f) = 0
      delta_k (E i f) <= delta_k f + C i k * delta_i f     for k /= i
  ```
  i.e. the Dobrushin matrix is the coordinatewise MAJORANT governing one-site
  oscillation transport.  Everything downstream is iteration.

  **Corrected 2026-08-02.**  This line read "is exactly what acts on oscillation
  vectors".  It is not: "exactly" would assert minimality, attainment or
  optimality, none of which follows, and it is the same confusion between a
  majorant and the minimal coefficient that cost two versions of the paper for
  `tanh|J|`.  The phrase had already been corrected in the desk's prose and
  survived here, in the charter that governs the rung.
* **D-3d — iteration to the comparison estimate**, consuming D-1.
* **D-3e — the covariance bound**, and only then the sentence D-3 exists for.

## THE ANALYTIC INGREDIENT that D-3c needs, named now

For two distributions `p, q` on a finite set and any `g`,
```
    | sum_s (p_s - q_s) * g_s |  <=  TV(p,q) * osc(g),      TV = (1/2) sum_s |p_s - q_s|.
```
This is where the constant of the window is decided.  A cheaper proof using a
fixed base point instead of the midpoint gives `2 * TV * osc(g)` and would
**halve the window** to `4 tanh|beta| + 4 tanh|gamma| < 1`.  **The cheap route is
allowed only if the sharp one fails, and taking it must be declared in the
module and in the paper, with the window restated.**  Registering this now so
that a later loss of a factor two cannot be presented as the intended design.

## PRE-REGISTERED JUDGES

`scripts/judge_dobrushin_d3.py`, committed in this same commit, BEFORE any Lean
of this rung.  Gates exit non-zero; none bundles a theorem with its witness;
each predicts a NUMBER, not a range.  Audit output is printed IN FULL --- no
`head`, no `cut` --- per Addendum 577.

* **J8 — the TV/oscillation inequality as an identity at its extremal case.**
  On pre-registered finite distributions the bound is checked, and a case where
  it is ATTAINED is exhibited.  A bound that is never attained would mean the
  constant is not the constant.
* **J9 — D-3c as a NUMBER, by brute force.**  On small explicit systems
  (`|S| = 2`, `|iota| <= 3`) with an explicit kernel, `delta_k (E i f)` and
  `delta_k f + C i k * delta_i f` are computed over ALL configurations and
  exhaustively over ALL **BOOLEAN** observables; the gate fails on any violation
  and reports the worst margin.  **This is the gate that can kill the rung before
  Lean is written.**

  **Corrected 2026-08-02.**  This line read "ALL observables in a spanning
  family".  Boolean observables are an exhaustive subclass, not a spanning family
  in any sense that would make the test conclusive for all real-valued
  observables --- the inequality is not linear in `f`, since `delta` is a
  supremum.  The gate is exhaustive within its class and the charter now says
  which class.
* **J10 — non-vacuity of the whole chain.**  An explicit system inside the
  window for which `D = sum_n C^n` is finite, the covariance of two explicit
  observables is computed by brute force, and the predicted bound is checked.
  If the predicted bound is violated, the comparison estimate as stated is
  WRONG and the campaign stops.

## PROHIBITIONS

1. Prohibitions 1-7 of `docs/DOBRUSHIN-CHARTER.md` remain in force.
2. **No infinite-volume state is constructed.**  Everything is finite sums over
   a finite configuration space; the limit, if ever taken, is taken at the level
   of the BOUND.
3. The comparison estimate is **classical** (Dobrushin 1968/1970; Simon,
   *Statistical Mechanics of Lattice Gases*, Ch. V).  Nothing here may be
   presented as new mathematics.  The novelty claimed is mechanisation and
   composition, exactly as in D-1/D-2.
4. **No claim that D-3 closes `sup_L specRatio(L) < 1`.**  Even complete, D-3
   yields decay of correlations; the operator transport through the finite-time
   interface to `volumeUniform_gap` is a further rung and is not this charter's.
5. If a rung fails, it is committed with its diagnosis, never deleted.

## ROLES AND ENVIRONMENT

This session fabricates and does not audit itself.  All Lean and all sweeps run
on the sanctioned Colab Linux plane; the desktop edits, commits and hashes only.

## KILL CRITERIA

* **J9 fails** on any small system -> D-3c as stated is false; stop, report, and
  do not attempt to repair by weakening the gate.
* **J10 fails** -> the comparison estimate as formulated here is wrong; stop.
* D-3c not closed in Lean after a declared budget -> report the state, keep the
  module with its diagnosis, and do not let the paper claim the rung.

## AMENDMENT 1 (2026-08-02) — where the zero diagonal enters, decided before D-3c

External reading, and correct: the agreed assembly
`B_i = I - e_i e_i^T + C^T e_i e_i^T` gives, coordinatewise,
`(B_i v)_k = v_k - [k=i] v_i + C_ik v_i`, hence `(B_i v)_i = C_ii v_i`.
Concluding `(B_i v)_i = 0` therefore requires a decision, and it must be a
DECLARED one rather than an accident of the physical instance, whose diagonal
happens to vanish.

**Decided: `C_ii = 0` is an explicit hypothesis of the matrix assembly, and of
nothing else.**  The split is:

* `deltaAt i (E i f) = 0` — a SEMANTIC result, independent of `C`, resting on
  the locality hypothesis that the conditional at `i` does not see the old value
  at `i`;
* `deltaAt k (E i f) ≤ deltaAt k f + C i k * deltaAt i f` for `k ≠ i` — consuming
  only that `C` is a MAJORANT off the diagonal, never that it is minimal;
* `delta (E i f) ≤ B_i * delta f` — the matrix form, and the ONLY statement that
  assumes `C_ii = 0`.

This keeps D-3c usable with any dominating interdependence matrix, which is the
same distinction that cost two paper versions for `tanh|J|`, and it stops the
zero from arriving by simplification.

**Also registered, as a reserve route for Popoviciu** if the algebraic
development is obstructed: with `c = (M+m)/2`, `abs_sub_mid_le` of D-3a already
gives `|f x - c| ≤ osc f / 2`, hence `E[(f-c)^2] ≤ osc(f)^2/4`, and the variance
translation identity `E[(f-c)^2] = Var f + (E f - c)^2` finishes.  Its formal
advantage is that the factor `1/2` is again born in exactly one lemma and the
`1/4` appears by squaring it, rather than through a second independent
normalisation.  Three endpoints stay separate either way:
`popoviciu_variance_le`, `gruss_covariance_le`, `gruss_attained`.

## AMENDMENT 2 (2026-08-02) — the banner is part of the audited bytes

Registered before any elaboration of D-3a, because it changes the shape of the
closure and not merely its paperwork.

`SOURCE, NOT RESULT` lives in a docstring and is inert to the compiler.  It is
NOT inert to the closure criterion, which is about BYTES: removing it changes the
file's SHA-256, so

```
    build of the file WITH the banner   does NOT certify
    the file WITHOUT it,
```

even though the only difference is a comment.  A green run on one set of bytes
says nothing about another set, and this lane does not get to make an exception
for differences it judges harmless — that judgement is exactly what an audit is
for.

**Sequence, fixed now:**

1. repair and elaborate D-3a **keeping** the banner, until the mathematics is
   green;
2. one FINAL SOURCE COMMIT `A` replacing the banner with a stable statement of
   formalised status;
3. from a CLEAN CHECKOUT OF `A`: focused build, five endpoints and the witness
   checked, focused oracle, SHA-256 computed;
4. hash — and preferably the build — repeated from a SECOND INDEPENDENT
   checkout;
5. a later DOCUMENTARY COMMIT `B` recording logs, hashes and oracle output,
   **without touching the Lean module again**.

`B` cites `A` without self-reference, and every reported result refers to exactly
the bytes of `A`.

**Until all of that holds, an intermediate green run means:** source that has
passed a local test.  Not a formalised result of this repository.

**Closure criteria for D-3a, complete list, conjunctive:** focused elaboration
succeeds; five endpoints compiled; the exact equality witness compiled;
non-emptiness explicit in the signature; a single convention for `TV` and for
`osc`; the factor `1/2` traceable to one lemma; the TV/oscillation corollary
obtained by REWRITING and not by a second proof under another convention;
stdout, stderr and exit code preserved OUTSIDE the VM; focused oracle clean;
SHA-256 reproduced from another checkout; and no subsequent modification of the
module.
