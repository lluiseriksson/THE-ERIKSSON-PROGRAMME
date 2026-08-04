> **Scope limitation — read before the title.** `Cross` does not participate
> in the effective weight or pairing, and reflection-induced inversion of
> `Cross` is not exercised. The product-form auxiliary weight is not a
> derivation of a lattice plaquette factorization. The analytic Haar
> positivity theorem for every continuous observable and the exact
> `Qβ(tr) ≥ β/4` bound are not weakened by this repair.

# Audit and repair record

Date: 2026-07-31

Status: **REPAIR COMPLETE; NOT AUTOAUDITED; FRESH BLIND PRE-AUDIT PENDING;
GATE 7 SUSPENDED**

No model output described below is used as mathematical evidence.

## Internal adversarial review

A separate read-only Codex review correctly found that the first endpoint
called the Haar kernel producer without connecting it to the declared cut,
that `Cross` was not integrated, and that the general algebraic split allowed
arbitrary unrelated half weights.  Those findings were treated as blocking,
not waived.

The remediation adds:

- `su2OnePlaquetteWilsonWeight`, the physical minimal-cut specialization with
  unit internal-half weights;
- `su2OnePlaquetteReflectedIntegrand`, which explicitly applies reflection and
  complex conjugation to the half-observable;
- `su2OnePlaquetteReflectedPairing`, which integrates left, crossing, and
  right SU(2) variables against normalized Haar measure; and
- `su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm`, the exact bridge
  consumed by the analytic positivity theorem.

The earlier remediation was incomplete. The product-form definition
`su2OnePlaquetteCutWeight` had been advertised as if a geometric
factorization had been derived. The theorem now named
`su2OnePlaquetteCutWeight_eq_undressedKernel` proves only that the common
gauge-pure transporter can be removed from the dressed kernel. No positivity
is claimed for arbitrary complex half weights, no lattice action is derived,
and the finite `ReflectionSplitting` consumer is not instantiated.

A later manufacturer-side audit of public PR #35 added three limitations:

1. the single crossing transporter is gauge-pure and does not exercise the
   general two-transporter plaquette;
2. `F = 1` proves non-nullity but does not isolate a nontrivial PSD mode; and
3. the `8179` job count belongs to the endpoint target, not global core.

The first and third are now explicit in `CERTIFICATION.md` and
`INTEGRATION-NOTE.md`.  The second is now closed by the preregistered
`Qβ(trace) ≥ β / 4` theorem chain recorded in `SHARP-GATE.md`.  This
manufacturer-side review and route design are not counted as terminal
external audit.

A later blind pre-audit found three blocking presentation/identification
defects despite the valid analytic chain: front-door overclaiming, geometric
vacuity of `Cross`, and presentation of a definitionally factorized weight as
a derived physical factorization. This repair addresses those findings
without changing the analytic Haar, Schur, exact `β / 4`, or tail-PSD
theorems. The repair is not permitted to certify itself; a new blind
pre-audit is pending.

## Fable High

The required account preflight was performed with profile `masterythief`.
It reported:

```text
loggedIn = true
email = masterythief@gmail.com
```

Four bounded calls were attempted: the initial audit/design call, one retry
at the original proof bottleneck, one retry at the preregistered `β / 4`
character bottleneck, and one final audit attempt after the sharp theorem
closed.  Before the final attempt, the account again reported
`loggedIn = true` and `email = masterythief@gmail.com`.  All calls returned
HTTP 429 with `is_error = true`, no usable response, no verified
`claude-fable-5` result, and empty `modelUsage`.  In accordance with the task
contract, there was no retry loop and no simulated audit.

## Opus 5 Max

One earlier local CLI response was rejected because its `modelUsage` contained
both `claude-opus-5` and an auxiliary Haiku entry; the contract required
exactly `claude-opus-5`.

A later bounded call used the required profile, cleared API-key/auth-token
environment variables, and requested the exact model identifier
`claude-opus-5` with effort `max`, JSON output, and no session persistence.
It timed out after 184 seconds and produced no JSON result or `modelUsage`.
Only the process created by that call was stopped.  It is not represented as
an audit.

## Consequence

The local build and axiom oracle are executable evidence only. Gate 7 is
suspended: no external audit is consumed, no paper is created, and this draft
PR must not be described as independently audited. The immediate next check
is a fresh blind pre-audit of the repaired source.

## Parked-state policy

Recorded on 2026-07-31 by the owner:

- Gate 7 is unchanged in substance and is now explicitly suspended;
- the owner chooses to wait rather than amend the gate;
- there is no known quota-reset cadence, so none is inferred or scheduled;
- exactly one retry is permitted, and only after independent evidence that
  the Fable quota has renewed;
- periodic retries, polling, and retry loops are prohibited.

A possible independence-based amendment was discussed but **not adopted**.
It is not part of the current contract and no amendment document is committed.
Only the owner may decide to adopt such an amendment if the external service
becomes indefinitely unavailable.

## Repair stop statement

**REPAIR COMPLETE; NOT AUTOAUDITED; FRESH BLIND PRE-AUDIT PENDING; GATE 7
SUSPENDED.**
