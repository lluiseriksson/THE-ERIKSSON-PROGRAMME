# Spatial vacuum pairing interval API failure 002

## Classification

Second instrumental failure before any interval or pairing result.  No
mathematical conclusion and no PASS.

## Immutable input

- Repository SHA: `4890ffc203c3fcf48378e11fab248ca2d864b50d`
- Script: `scripts/probe_spatial_vacuum_pairing.py`
- Script SHA-256:
  `42761ec083f2dbd3388ef7d8c574e599419ed697033ca796edfad4722be097f1`
- Environment: Python 3.12.6, mpmath 1.3.0, Windows 11 build 26200

## Command and observed failure

```text
python scripts/probe_spatial_vacuum_pairing.py
```

The command returned exit code 1 after 0.272819 s.  Its LF-terminated combined
output has SHA-256
`d904c6e51c36675794de7049a11054858e5ce600bfff2d7f34d4c3bbc42f5d23`.
The decisive literal traceback ended with:

```text
AttributeError: 'MPIntervalContext' object has no attribute 'sinh'. Did you mean: 'sin'?
```

The previous repair had replaced unavailable `iv.tanh` by `iv.sinh/iv.cosh`;
mpmath 1.3.0's interval context exposes none of those hyperbolic methods.  The
failure again occurred before an interval enclosure, pairing record, JSON
status, or optimized run.  No point values computed before the failing call
were emitted or accepted.

## Repair boundary

All interval hyperbolic functions must be expanded through the elementary
identities

```text
cosh(x) = (exp(x) + exp(-x))/2
sinh(x) = (exp(x) - exp(-x))/2
acosh(x) = log(x + sqrt(x*x - 1))
```

using only interval primitives.  That repair belongs to a later commit.  No
Lean, Lake, oracle, Colab runtime, or sustained computation was started.
