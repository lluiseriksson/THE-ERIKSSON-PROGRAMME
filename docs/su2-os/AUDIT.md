# External audit record

Date: 2026-07-30

Status: **NOT PASSED — external service failure**

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
  consumed by the final positivity endpoint.

The general `leftWeight`/`rightWeight` factorization theorem is only an
algebraic splitting identity; no positivity is claimed for arbitrary complex
half weights.  The certified physical endpoint is the unit-internal-weight
one-plaquette cut, not a theorem for an arbitrary lattice action.

A second read-only pass confirmed that the reflected-pairing and crossing
integration findings are closed for this minimal declared model.  The residual
scope boundary remains explicit: this weight is not derived from the
repository's `GaugeConfig.plaquetteHolonomy`/`wilsonAction` API, and it does
not instantiate the finite `ReflectionSplitting` consumer.

A later manufacturer-side audit of public PR #35 added three limitations:

1. the single crossing transporter is gauge-pure and does not exercise the
   general two-transporter plaquette;
2. `F = 1` proves non-nullity but does not isolate a nontrivial PSD mode; and
3. the `8179` job count belongs to the endpoint target, not global core.

The first and third are now explicit in `CERTIFICATION.md` and
`INTEGRATION-NOTE.md`.  For the second, `SHARP-GATE.md` preregisters
`Qβ(trace) ≥ β / 4`; Lean now certifies the exact zero Haar mean of `trace`,
but not yet the lower bound.  This manufacturer-side review is not counted as
terminal external audit.

## Fable High

The required account preflight was performed with profile `masterythief`.
It reported:

```text
loggedIn = true
email = masterythief@gmail.com
```

Three bounded calls were attempted: the initial audit/design call, one retry
at the original proof bottleneck, and one retry at the new preregistered
`β / 4` character bottleneck.  All returned HTTP 429 with `is_error = true`,
no usable response, no verified `claude-fable-5` result, and empty
`modelUsage`.  In accordance with the task contract, there was no retry loop
and no simulated audit.

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

The Lean endpoint, local build, and axiom oracle are complete, but terminal
gate 7 remains externally blocked.  No paper is created, and this draft PR
must not be described as independently audited until a later compliant model
call returns and its conclusions are checked against the source.
