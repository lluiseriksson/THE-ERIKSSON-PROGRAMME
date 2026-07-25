# Incident: rescue-300 width-1 box fails at a strict cover cell

The preregistered rescue-300 contract was run on
`beta=[3297/32,3329/32]` with CWIN `3/2`, beta order `40`, t order `50`,
Arb precision `300`, and `MIN_DT=1/100000`.  After approximately 87 minutes
of CPU the recursive cover raised:

```text
RuntimeError: bulk failure near t=2.3806982257566736
```

No production transcript was emitted and no manifest was changed.  This is a
negative design result: width `1` is not an admissible terminal unit under the
frozen rescue-300 contract.  The verified width-`1/2` route remains the active
fallback; this incident does not promote or invalidate any existing unit.
