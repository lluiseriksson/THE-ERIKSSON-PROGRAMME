# Charter — the stabiliser of the projective diameter

Registered 2026-08-02, **before any theorem was written**, under the standing
regime: judges before pages, split roles, measured failure committed with its
diagnosis.

## The question

The submitted paper (*Congruence Rigidity and the Fusion Bound*, viXra 18179797)
proves `Δ(DMD) = Δ(M)` for `D` positive diagonal and builds its whole thesis on
it: a positive weight moves the spectrum but cannot move the geometry.  Its §8
leaves open what happens for congruences by positive matrices that are **not**
diagonal.  This is that question.

Two candidate statements, neither claimed:

* **(MONOTONE)** For every entrywise positive `S`, `Δ(S M Sᵀ) ≤ Δ(M)`.
  A genuinely mixing congruence can only *contract* the projective geometry.
* **(STABILISER)** Equality holds for **all** `M` exactly when `S` is monomial —
  a positive diagonal times a permutation.

If both hold, the consequence for the submitted paper is sharp and is the reason
to want them: since `sup_D r(DMD) = tanh(Δ/4)` and `Δ` can only decrease under
mixing, **the diagonal group is precisely the stabiliser of the obstruction**,
and any weight action that genuinely mixes strictly lowers the reachable
supremum.  The fusion bound belongs to the diagonal group and nothing larger.

## Reconnaissance already run — evidence, NOT judges

`scripts/probe_stabilizer.py`, before this charter existed:

* sanity: diagonal, permutation and monomial `S` give `|ΔΔ| ≤ 4.4e-16`;
* MONOTONE: 900 random cells at `n = 3,4,5`, **no increase ever**, worst change
  `-0.40 / -0.80 / -0.92`;
* STABILISER: equality exactly at the monomial point, strictly negative gap
  already at a perturbation of `1e-4`.

Under the owner rule of 2026-08-01 a gate whose verdict I already know cannot be
my judge.  These are recorded as evidence and are **not** the gates below.

Also recorded, and it closes a different door cheaply: the companion question
"how *low* can a weight push `r`?" has a one-line answer — concentrating on a
single site sends `r → 0` (for the `2×2`, `det = ε²(1-μ²)` against `tr = 1+ε²`).
The infimum is `0`, the supremum is `(1-μ)/(1+μ)`, and connectedness of the
orbit fills the interval.  Not a paper; recorded so nobody spends a week on it.

## Pre-registered gates (harder than what has been run)

**JA — MONOTONE, adversarial.**  `S` chosen to *try* to increase `Δ`, not drawn
uniformly: near-singular `S`; rows differing by `10^4` in scale; a single
dominant entry; `n` up to 8; and `M` near-degenerate (`μ ≤ 10^-3`).
*Prediction, registered now:* `Δ(SMSᵀ) - Δ(M) ≤ 10^-9` in **every** cell.
One strict increase kills MONOTONE and the paper is rewritten around the
counterexample.

**JB — STABILISER, the risky half.**  The direction that needs a witness for
each non-monomial `S`.  For 200 random non-monomial `S`, a search over `M` must
fail to reach equality: `min_M (Δ(M) - Δ(SMSᵀ)) > 10^-6`.
*Prediction:* the gap stays bounded away from zero and shrinks continuously to
`0` as `S` approaches the monomial group.  If some non-monomial `S` preserves
`Δ` for all `M`, STABILISER is false as stated and must be replaced by the
correct group, whatever it turns out to be.

**JC — Lean.**  Zero errors, zero warnings, oracle reconciled per declaration,
zero `sorryAx`, and the aggregate job count measured, not predicted.

## Intended proof, recorded so a failure is diagnosable

`Δ(M)` is the Hilbert projective diameter of the *columns* of `M`:
`Δ(M) = max_{k,l} d_H(col_k M, col_l M)`, since
`d_H(x,y) = log max_{i,j} (x_i y_j)/(x_j y_i)` is exactly the cross-ratio.

MONOTONE then needs only two elementary facts, and **neither is the hard
Birkhoff theorem**:

1. a positive matrix is *non-expansive* in the Hilbert metric — one line, from
   `x ≤ c y ⟹ Sx ≤ c Sy`.  The difficulty in Birkhoff–Hopf is the contraction
   *constant* `tanh(Δ/4)`, which is not needed here;
2. the Hilbert diameter of positive combinations does not exceed the diameter of
   the generators.

If the write-up ends up importing Birkhoff–Hopf, that is a signal the argument
drifted, and it stops for re-derivation.

## Death criteria

1. One strict increase in JA ends MONOTONE as stated.
2. A non-monomial `S` preserving `Δ` for all `M` ends STABILISER as stated.
3. If the proof needs the Birkhoff contraction constant, stop and re-derive.
4. No claim about the submitted paper's physics is strengthened by this work:
   this classifies a group, it does not prove anything new about any model.
