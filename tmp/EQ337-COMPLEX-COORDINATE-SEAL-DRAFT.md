# Eq337 complex-coordinate seal draft

Status: **PRE-VALIDATION / NOT CHECKED** until the exact v3 Colab gate emits
`FINAL_STATUS=PASS` and the local fail-closed evidence packager accepts the
executed notebook.

- source checkpoint: `b91d42630efb15f32d4b4ecd242a33238926d4de`
- runner checkpoint: `1d306a29935de6a8e02825ee2d0ed4f36ad62e34`
- notebook checkpoint: `0fc811db96087d8968dcadfb6a11aa6317f9e58a`
- runner revision: `eq337-complex-coordinate-fresh-v3`
- runner Git-blob SHA-256:
  `1EF0CA01D63BFD8A95382E4849DB762DF9E0654316A51B213A26EB9BCB61B6FA`
- boundary: three source/audit pairs, six files
- declaration/readout coverage: `57/57` (`8 + 23 + 26`)
- seal preview: seven files (six boundary files plus `YangMillsCore.lean`)
- sealed manifest SHA-256:
  `3F9B5A7D4B833A0523859B539563A5ACEBA4D06210ABBB58396A2C71C74A5542`

## Evidence placeholders

- focal exits/times: `[PENDING]`
- audit exits/times: `[PENDING]`
- executed-notebook SHA-256: `[PENDING]`
- verifier JSON SHA-256: `[PENDING]`
- runner evidence SHA-256: `[PENDING]`
- runner archive SHA-256: `[PENDING]`
- local package manifest SHA-256: `[PENDING]`

Acceptance requires all seven queue stages to exit zero, exactly one permitted
axiom readout for each of the 57 public declarations, no `sorryAx` or
`ofReduceBool`, exact source/blob pins and one `FINAL_STATUS=PASS`.  Only then
may `tmp/seal_eq337_complex_coordinate_prevalidation.py --apply` retire the
six PRE-VALIDATION markers and import the three audits into the root.

This seal is the real/complex coordinate and perturbed-background boundary
for CMP99 (3.37).  It does not construct the regional precision or Green,
attain window 15, close rows 23--24, move `20/41`, or instantiate
`TermSource`.
