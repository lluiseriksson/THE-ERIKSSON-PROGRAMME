# K2 R7/R8 and Cauchy budget — Opus 5 Max audit (2026-07-28)

## Model and account verification

The bounded audit was run through the explicitly selected local profile
`masterythief` after clearing API-key environment variables.  The raw JSON
reports:

```text
is_error = false
modelUsage contains exactly claude-opus-5 as the reasoning model
modelUsage also contains a small claude-haiku-4-5 auxiliary call
```

The auxiliary Haiku use is allowed by the standing model policy and is not a
fallback.  The full response is preserved at
`outputs/opus5-r7-r8-cauchy-audit-20260728.json`.

Two attempted Fable Bridge audits in the same work session were rejected:
one timed out without model verification and the other returned
`claude-opus-4-8` with `verified_fable_5=false`.  Neither response is cited
as Fable 5 or used as evidence.

## Accepted findings

The audit independently confirmed the order bookkeeping, subject to unit
denominators and exact cancellation:

- `Y=B/(2*c*delta*KD^2)` through `Y7` requires `B` through `delta^8`;
- because `h=O(delta)`, a companion through `h^8` is sufficient at that
  order;
- the constant coefficient of `B` must cancel exactly before division by
  `delta`;
- every internal reciprocal must have nonzero constant term;
- exact arithmetic must contain no SymPy `Float`;
- a guard run at `O(delta^11)` with companions through `h^10` should leave
  `Y0,...,Y7` unchanged;
- the complex certificate must establish the square-root branch and the
  absence of KD zeros on the disk, not merely on sampled points;
- interval theta arcs, not point sampling, are required for the circle
  supremum;
- true-companion and exterior errors must receive separately declared
  real-axis budgets.

The guard run and explicit structural assertions are therefore added to the
acceptance chain before any exact-head promotion.

## Independently rejected budget objection

Opus warned of a possible factor `Delta^(-2)` error.  That objection does not
apply to the implemented budget.

Put

```text
L = theta3 - |Y2 + Y3*Delta + ... + Y7*Delta^5|,
q = Delta/rho.
```

The driver computes

```text
available = L*Delta^2,
multiplier = q^8/(1-q),
required_M = available/multiplier.
```

For any `0 < delta <= Delta`, Cauchy gives

```text
tail(delta) <= M*(delta/rho)^8/(1-delta/rho).
```

After division by `delta^2`, the right-hand side is increasing in `delta`,
so the worst point is `Delta`.  The equivalent coefficient-level condition
is

```text
M/rho^2 * q^6/(1-q) <= L.
```

The two thresholds are exactly equal:

```text
L*Delta^2 / (q^8/(1-q))
 = L*rho^2 / (q^6/(1-q))
 = L*rho^8*(1-q)/Delta^6.
```

Numerically both yield

```text
required_M = 47.26356847029885
```

after retaining through `Y7`.  The audit's claimed factor `10^6` arose from
comparing `M*q^8/(1-q)` directly with `L`, whereas the code compares it with
`L*Delta^2`.

## Scope disposition

The audit correctly observes that the finite polynomial-companion surrogate
is not yet the theorem's true carrier.  This is already an explicit scope
barrier, not a promoted assumption.  A green complex-circle run will remain
conditional evidence until:

1. the true Bessel companion error is bounded on the positive real axis;
2. the fixed-square exterior is bounded uniformly;
3. the resulting charges fit a preregistered split of the K2 budget.

No manuscript slot or theorem gate is changed by this audit.
