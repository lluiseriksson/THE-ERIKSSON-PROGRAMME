# C6d Green-owner cold-gate failure

- Classification: `FAIL` (compiler), stop-on-first-error.
- Source checkpoint: `86d9f0e44a17e6f80667257e4ecfd814a67adaed`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Toolchain asset SHA-256: `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
- Runtime opened: `2026-08-29T20:31:30.881606+02:00`.
- Evidence closed: `2026-08-29T21:46:34.773870+02:00`.

## Executed stages

- `01_cmp99eq342leftderivativefromvaluebound_focal`: exit `0`, 4283.665 s.
- `01_cmp99eq342leftderivativefromvaluebound_audit`: exit `0`, 8.773 s.
- `02_cmp99eq342rightadjointfromvaluebound_focal`: exit `1`, 74.987 s.

## First real error

`YangMills/RG/BalabanCMP99Eq342RightAdjointFromValueBound.lean:58:21: unexpected token '⇒'; expected '↦', '=>'`

The source used `fun middle source ⇒`; the follow-up patch changes only that token to
Lean's accepted ASCII lambda separator `=>`. The subsequent unsolved goal in the same
stage is downstream of this parse error and is not classified independently.

This evidence does **not** seal stage 02 or any later stage, does not remove any
`PRE-VALIDATION` marker, and does not move `20/41`, `TermSource = 0`, or window 15.

## Preserved artifacts

- `hrpoly-c6d-green-owner-prefix-evidence.tar.gz` SHA-256:
  `DE1EC873DC7890C36EDD386A7779BADA75502FE7988012948B8FDFA8A1889A25`.
- Executed notebook `colab_c6d_green_owner_prefix_validation.ipynb` SHA-256:
  `2EBEF0DF33CFF89124BB734F36728224B77FC54E26970A78BD29700CEF680463`.
- Inner evidence archive SHA-256 reported by the Colab runner:
  `8c09c086f1c7253395ee2b04ca0d54e416411afdde1ba514d96ac57f97b81013`.

The extracted `evidence.json` and stage stdout files are retained beside this record.
