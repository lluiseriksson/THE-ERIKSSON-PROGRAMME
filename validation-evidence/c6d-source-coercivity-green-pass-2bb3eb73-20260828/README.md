# C6d source coercivity/Green cold PASS

Classification: cold intermediate seal evidence.  This validates the exact
source-fixed C6d coercivity and baseline Green chain; it does not attain
window 15, move `20/41`, or instantiate `TermSource`.

- source SHA: `2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24`
- runner revision: `c6d-source-coercivity-green-v1`
- Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- root: `lake build YangMillsCore`, `11060` jobs, exit `0`, `8843.896` s
- recorded stages: `37`, all exit `0`
- total recorded stage time: `12089.008` s
- audited public declarations: `80`, each using only
  `{propext, Classical.choice, Quot.sound}` or a subset
- evidence JSON SHA-256:
  `AA4A747F01008F68BC7AA413949BF0A189542C296D4A556CF38B7FB14234BBEA`
- sealed-manifest SHA-256:
  `9E2BFFCB5D4F54E1464566C00CBA5F89FCC823D43A75D305F71303D876F1D80D`

The external verifier audits the exact archive topology, stage sequence,
per-stage output hashes and axiom blocks from the archive.  The executed
notebook is separately checked for its one original executed code cell,
terminal PASS sentinel and printed evidence/archive hashes.  This split is
required because Colab persists only the tail of very long streaming output.

