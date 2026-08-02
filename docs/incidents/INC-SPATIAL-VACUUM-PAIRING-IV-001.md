# Spatial vacuum pairing interval API failure 001

## Classification

Instrumental failure before any interval or pairing result.  No mathematical
conclusion and no PASS.

## Immutable input

- Repository SHA: `e3a95e0127fe7cef4b5a49c8a67c3f294d8c935a`
- Script: `scripts/probe_spatial_vacuum_pairing.py`
- Script SHA-256:
  `2399c81fe8d60d2d9612bbe8917b5ad1aa724d3f709729462c3d91d9887aa4ac`
- Environment: Python 3.12.6, mpmath 1.3.0, Windows 11 build 26200

## Command and observed failure

```text
python scripts/probe_spatial_vacuum_pairing.py
```

The command returned exit code 1 after 0.409930 s.  Its LF-terminated combined
output has SHA-256
`98393dd895153d0626e97190b4de54d28ed360c9aea919daf546bda246d22940`.
The decisive literal traceback ended with:

```text
AttributeError: 'MPIntervalContext' object has no attribute 'tanh'. Did you mean: 'tan'?
```

The failure occurred while constructing the interval dual coupling, before
the interval enclosure, pairing records, JSON status, or optimized run.  The
point-precision values computed earlier in the process were not emitted and
are not claimed as evidence from this run.

## Repair boundary

The interval identity `tanh(x) = sinh(x) / cosh(x)` can avoid the unavailable
API without changing the mathematical formula.  That repair must be a later
commit.  This incident remains as the record of the failed immutable script.

No Lean, Lake, oracle, Colab runtime, or sustained computation was started.
