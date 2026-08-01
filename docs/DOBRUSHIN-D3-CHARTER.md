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
  i.e. the Dobrushin matrix is exactly what acts on oscillation vectors under a
  single-site update.  Everything downstream is iteration.
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
  `delta_k f + C i k * delta_i f` are computed exactly over ALL configurations
  and ALL observables in a spanning family; the gate fails on any violation and
  reports the worst margin.  **This is the gate that can kill the rung before
  Lean is written.**
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
