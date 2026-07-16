# Incident G5: finite bridge fails at the beta-20--25 endpoint

**Date:** 2026-07-16  
**Scope:** exploratory design only; no theorem load  
**State:** route rejected under the frozen one-band probe

The authorized diagnostic used the existing five-family finite-G5 judge with
the exact new delta band

```text
[1/25, 1/20]  =  [0.04, 0.05]
```

This is the missing `20 <= beta <= 25` band.  The first 19 angular cells were
strictly positive, but the registered adversarial final cell
`lambda_index=74`, `lambda in [74/50,75/50]`, required the mixed-resolution
fallback and failed:

```text
B0_lower = -0.00106925913378300578246467800204
H_lower  = -0.178827006369829177856445312500
```

The full 75-cell run was stopped by the time limit after the same positive
prefix; the endpoint failure is independently decisive for this fixed band
and architecture.  No beta subdivision, delta-band movement, precision
increase, or production transcript is inferred.  The G5 union slot therefore
remains open on `20 <= beta < 25`; any replacement endpoint-cancellation route
requires a new pre-registration.
