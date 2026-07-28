# G2 split-unit result — 2026-07-24

The monolithic order-30/t-order-37 cover timed out on the first high-
order boxes above beta 81.  A fixed, preregistered partition in `t` was
therefore implemented and tested on the single beta box `[81,325/4]`.

The five intervals are `[3/5,3/2]`, `[3/2,9/4]`, `[9/4,3]`,
`[3,61/20]`, and `[61/20, pi_up-(3/2)/81]`.  Production and replay
both terminate with 246 rows, every Arb upper endpoint is strictly below
zero, and the transcript files are byte-identical.  The complete provenance
is in `run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-81-81p25-20260724.json`.

This is a useful engineering result, not a theorem closure.  It covers one
candidate box only; it does not prove the analytic relay from the scaled sign
rows to `(H_tail)`, does not cover the four G2 gaps, and cannot promote G2,
K4, S1'''/S2''', or G6.  Any extension must retain explicit partitions,
production/replay equality, current dependency hashes, and the same
candidate-only scope until the missing relay lemma is proved independently.

The adjacent box `[325/4,163/2]` was subsequently run with the same driver.
Its production/replay pair also has 246 rows, byte equality, and strict
negative upper endpoints; its separate provenance is recorded in
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-81p25-81p5-20260724.json`.

The next adjacent box `[163/2,327/4]` likewise passes production/replay with
247 rows and strict negative upper endpoints.  Its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-81p5-81p75-20260724.json`.

The next box `[327/4,82]` also passes with 247 rows and byte-identical
production/replay.  Provenance is recorded in
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-81p75-82-20260724.json`.

The adjacent box `[82,329/4]` passes with 247 rows as well; its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-82-82p25-20260724.json`.

The next box `[329/4,165/2]` passes with 248 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-82p25-82p5-20260724.json`.

The next box `[165/2,331/4]` passes with 249 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-82p5-82p75-20260724.json`.

The next box `[331/4,83]` passes with 250 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-82p75-83-20260724.json`.

The next box `[83,333/4]` passes with 250 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-83-83p25-20260724.json`.

The next box `[333/4,167/2]` passes with 250 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-83p25-83p5-20260725.json`.

The next box `[167/2,335/4]` passes with 251 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-83p5-83p75-20260725.json`.

The next box `[335/4,84]` passes with 251 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-83p75-84-20260725.json`.

The next box `[84,337/4]` passes with 252 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-84-84p25-20260725.json`.

The next box `[337/4,169/2]` passes with 252 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-84p25-84p5-20260725.json`.

The next box `[169/2,339/4]` passes with 252 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-84p5-84p75-20260725.json`.

The next box `[339/4,85]` passes with 254 rows and byte-identical replay;
its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-high-split-84p75-85-20260725.json`.
