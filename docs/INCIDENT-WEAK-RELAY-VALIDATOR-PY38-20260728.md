# Incident — weak-relay validator used a Python 3.9 string method

**Date:** 2026-07-28

**Scope:** validation harness only; no interval was parsed and no theorem
claim changed.

The first production attempt of
`validate_surface_high_beta_lambda3_weak_relay_inputs.py` ran under the
available Python 3.8.10 interpreter and stopped at
`str.removeprefix`, which is unavailable before Python 3.9.  Stdout is empty
and stderr contains the `AttributeError`.  Both files are preserved as:

```text
outputs/surface-lambda3-weak-relay-input-validation-production-20260728.txt
outputs/surface-lambda3-weak-relay-input-validation-production-20260728.stderr.txt
```

The repair replaces the two `removeprefix` calls by exact prefix-length
slices.  No threshold, transcript, dependency check, decimal parser, or
acceptance predicate changes.  Production and replay after the repair use
the suffix `-v2`; the failed paths are not overwritten.
