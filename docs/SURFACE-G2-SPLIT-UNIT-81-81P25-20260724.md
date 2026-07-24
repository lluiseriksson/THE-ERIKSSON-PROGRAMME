# G2 split-unit result — 2026-07-24

The monolithic order-30/t-order-37 cover timed out on the first high-
order boxes above beta 81.  A fixed, preregistered partition in `t` was
therefore implemented and tested on the single beta box `[81,325/4]`.

The five intervals are `[3/5,3/2]`, `[3/2,9/4]`, `[9/4,3]`,
`[3,61/20]`, and `[61/20, pi_up-(3/2)/81]`.  Production and replay
both terminate with 246 rows, every Arb upper endpoint is strictly below
zero, and the transcript files are byte-identical.  The complete provenance
is in `run-manifests/surface-scaled-bulk-cwin3p2-high-split-81-81p25-20260724.json`.

This is a useful engineering result, not a theorem closure.  It covers one
candidate box only; it does not prove the analytic relay from the scaled sign
rows to `(H_tail)`, does not cover the four G2 gaps, and cannot promote G2,
K4, S1'''/S2''', or G6.  Any extension must retain explicit partitions,
production/replay equality, current dependency hashes, and the same
candidate-only scope until the missing relay lemma is proved independently.

The adjacent box `[325/4,163/2]` was subsequently run with the same driver.
Its production/replay pair also has 246 rows, byte equality, and strict
negative upper endpoints; its separate provenance is recorded in
`run-manifests/surface-scaled-bulk-cwin3p2-high-split-81p25-81p5-20260724.json`.
