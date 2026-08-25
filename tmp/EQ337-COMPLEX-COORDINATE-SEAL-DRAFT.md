# Eq337 complex-coordinate seal draft

Status: **PRE-VALIDATION / NOT CHECKED** until the exact v4 Colab gate emits
`FINAL_STATUS=PASS` and the local fail-closed evidence packager accepts the
executed notebook.

- source checkpoint: `b70735b82216a0ab1cd9a3bd4e195db1426a83fe`
- runner checkpoint: `737b7b01badeba5811b1bb7ae557c6ea45c4a79e`
- notebook checkpoint: `d07aa0267c0e5b3a43d8f091a77759da39161fd3`
- runner revision: `eq337-complex-coordinate-fresh-v4`
- runner Git-blob SHA-256:
  `E88D83C8636FE3B20DA9B381212020BD6729FD7D8F121F44E448ECB766CA3D69`
- boundary: three source/audit pairs, six files
- declaration/readout coverage: `57/57` (`8 + 23 + 26`)
- seal preview: seven files (six boundary files plus `YangMillsCore.lean`)
- sealed manifest SHA-256:
  `9D989D470DB17507E09CF766226CB2DE843860D4450444A7788D26A5B7822165`

The earlier v3 gate is superseded before execution: its source spelled the
algebraic linear-equivalence notation with Unicode subscript digit one
(`≃₁`) instead of subscript ell (`≃ₗ`).  The v4 source changes exactly that
character; no compiler result is inferred from the textual correction.

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
