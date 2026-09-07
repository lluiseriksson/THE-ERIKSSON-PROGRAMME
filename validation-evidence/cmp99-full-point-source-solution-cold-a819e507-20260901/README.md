# Full periodic Eq. (2.46) point-source solution: cold seal

- source SHA: `a819e5074a9f58fb7ae7b93c6369a186956419a2`
- runner revision: `cmp99-full-point-source-solution-cold-v2`
- Lean: `4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- runtime: Colab Pro+ CPU, 50.99 GiB RAM
- final status: `PASS`

The cold focal queue compiled `FibreAction` and the full periodic point-source
solution, then ran both exact six-declaration axiom audits. All twelve audited
declarations depend on subsets of `propext`, `Classical.choice`, and
`Quot.sound` only.

Stage timings:

- `full_complex_precision_fibre_action_focal`: 1303.011 s, exit 0
- `full_complex_precision_fibre_action_audit`: 9.685 s, exit 0
- `full_point_source_solution_focal`: 169.021 s, exit 0
- `full_point_source_solution_audit`: 9.544 s, exit 0

Durable hashes:

- `evidence.tar.gz`: `6FD29196320213E76F8E3A4C40CF855019EC861C611DCC06479E32086AEB63FF`
- `executed.ipynb`: `341B3F0E84061E0342FE86C79B82A93073062CE8D8D83215A244B3EFA11B884B`

Independent local verification checked the evidence JSON, all four real exit
codes, the one-cell/one-execution notebook shape, the unique `FINAL_STATUS=PASS`,
the absence of `FINAL_STATUS=FAIL`, `sorryAx`, and `ofReduceBool`, and the exact
twelve-declaration axiom gate.

This is infrastructure for the later Green/inverse-uniqueness identification.
It does not attain window 15, move `20/41`, or construct a `TermSource`;
`TermSource = 0` remains exact.
