# Source lock — Eq. (2.31) P-family carrier/source target

Fill this before promoting any Eq. (2.31) carrier or admissibility statement.

## Required extraction

- exact printed/PDF page for CMP116 page 12 and pages 18–19;
- source definition of the eligible P-family;
- positive-oriented bond encoding used for the factor `Fin 4`;
- statement that the base cube / first coordinate of every eligible bond lies in
  the gap represented by `gapCubes`;
- distinction between carrier upper bound and lower bound on `|P|`.

## Lean target split

```text
source_subset_gapCarrier
mem_iff_source
admissible_iff_source
```

Do not merge these into one opaque proposition.
