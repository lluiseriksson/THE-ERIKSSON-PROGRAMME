# Incident: uniform `exp(4)` high-beta G5 ledger fails

**Observed:** 2026-07-28

**Affected design:** `SURFACE-HIGH-BETA-G5-LAMBDA4-PREREG-20260728.md`

## Result

The frozen uniform-tail design was tested at the beginning, middle, and end
of its lambda range.  The first cells of the middle and end units failed
after the allowed mixed refinement:

```text
lambda=[3,3.02], delta=[0,0.001]:
P0_lower=-0.0035636065..., H_lower=-0.10859599...

lambda=[3.8,3.82], delta=[0,0.001]:
P0_lower=-0.0171299181..., H_lower=-0.26853692...
```

`B0` remained positive.  The first unit emitted seven positive rows near
`lambda=2` before it was stopped once the global ledger had been
falsified.  Partial positive rows carry no theorem load.

## Diagnosis and successor

The central five-family values are charged in every cell by the worst-case
near-tail factor `exp(4)`.  This is valid but unnecessarily wide below the
right endpoint.  The successor freezes the same rational lambda cells but
uses the local outward endpoint `exp(lambda_hi)` in each cell.  This is a
strictly smaller instance of the same proved tail formula, not a posterior
change to a numerical tolerance.

The failed transcripts remain in the local audit archive and are excluded
from every production union.
