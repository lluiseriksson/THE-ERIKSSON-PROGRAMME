# JUDGES RUN 1 — verdict FAIL, and what the failure bought

Charter `docs/CONGRUENCE-CHARTER.md`, registered at commit `49311bad`.
Judges run afterwards, transcript in `judges-run-1.txt` (both modes, identical).

**The charter is not edited by this document.**  A pre-registration that gets
rewritten after its verdict is not a pre-registration.  This is a separate
record of what the gates said and what follows.

## JA — PASS

| L | β | tanh(βL) | deficit@γ=1 | deficit@γ=3 | fitted slope |
|---|---|---|---|---|---|
| 3 | 0.20 | 0.537050 | 8.481e-02 | 1.702e-03 | **−1.9577** |
| 4 | 0.20 | 0.664037 | 1.228e-01 | 2.366e-03 | **−1.9776** |
| 5 | 0.15 | 0.635149 | 1.531e-01 | 3.090e-03 | **−1.9566** |
| 4 | 0.35 | 0.885352 | 8.278e-02 | 1.277e-03 | **−2.0810** |

Predicted `p = 2`, band `[−2.10, −1.90]`; all four inside.  This is the judge
that mattered for the *explanation* rather than the *limit*: the deficit decays
like `e^{−2γ}` because the cheapest non-ferromagnetic configurations carry one
domain wall (weight ratio `e^{−2γ}`, diagonal ratio `e^{−γ}`, second-order shift
`e^{−2γ}`).  The account of the mechanism survives, not just the value.

## JB — FAIL, and it is the useful kind

Predicted: **at least 1 of 12** indefinite witnesses would exceed
`(1−μ)/(1+μ)`.  Observed: **0 of 12**.  Every one of the twelve — minimum
eigenvalues from −0.061 to −0.424 — landed on the bound to between 1.1e-16 and
1.6e-15.  Not near it.  On it.

The charter pre-specified the consequence, so there is nothing to negotiate:

> *"A sweep in which none exceeds it means I do not know why I am assuming
> positive definiteness, and the hypothesis must be either dropped or justified
> before it goes to ink."*

**Consequence, executed:** the positive-definiteness hypothesis is **dropped**
from the conjecture.  The statement that goes forward is

> **Conjecture (least-correlated pair).**  Let `M` be symmetric with `M_ii = 1`
> and `0 < M_ij < 1` for `i ≠ j`, and let `μ = min_{i≠j} M_ij`.  Then
> `sup_{D>0 diagonal} r(D M D) = (1−μ)/(1+μ)`, approached and not attained.

No definiteness assumption.  This is **stronger** than what the charter
registered, and it is stronger because a gate I wrote to protect a hypothesis
told me the hypothesis was not doing any work.

## What this does NOT license

* It does not make the conjecture proved.  It is still a conjecture with
  certified numerics and no proof, and prohibition 3 of the charter still binds
  every sentence about it.
* It does not extend to `M` with a **zero** or **negative** off-diagonal entry;
  nothing here tested that, and `μ ≤ 0` makes the target `≥ 1`, which is a
  different regime.
* It does not extend past the tested sizes (`n ≤ 6`) or past the tested
  indefiniteness (`λ_min ≥ −0.43`).  A witness with a large negative eigenvalue
  could make `|λ₀|` the *negative* extreme, and then `r` is measuring something
  else.  **Untested, and named here so it is not quietly assumed.**

## Standing consequence for the ink

Two claims of mine were wrong today and both are recorded rather than repaired
in place: the adversarial probe that printed `REFUTED` for a failed
precondition, and this hypothesis I could not justify.  Neither was caught by
review.  Both were caught by an instrument that was allowed to disagree with me.
