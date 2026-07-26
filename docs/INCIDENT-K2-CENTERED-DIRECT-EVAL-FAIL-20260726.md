# K2 centered direct evaluation — terminal failure (2026-07-26)

The preregistered direct evaluation in the centered variable was run and
replayed byte-identically on the critical index 144 cell.

```text
production/replay SHA-256: F1C3675FFC59FC0939696D00F632908EF917F0A63E1244078859252A9FC0A334
git head: 62b490d7b67585357098a4e6322c84e1015c1a68
script SHA-256: ee07793777ab7e9eb32b49c7cfcca9a508bf8d800e3ed4cda8d0ca9a4cccf10e
K_D center lower: 2.4428888922198018...
Y box: +/- 9.02
budget minimum: 0.00024 +/- 6.29e-6
raw margin lower: -9.25490211291410...
tail proxy (unresolved): 3.70e-6
terminal verdict: CENTERED DIRECT EVAL RAW FAIL; SINGLE CELL TERMINAL
```

The failure is caused by the broad moment/radius enclosure in the quotient,
not by the fifth-order truncation proxy. It rejects this direct-evaluation
assembly on the frozen cell. The centered denominator cover remains a useful
conditioning diagnostic only; no K2/G2/G6/manuscript state changes.
