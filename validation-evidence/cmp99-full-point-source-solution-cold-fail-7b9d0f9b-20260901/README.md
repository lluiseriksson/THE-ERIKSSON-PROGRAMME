# CMP99 full point-source solution cold FAIL evidence

- Source: `7b9d0f9b9e292d48c479477aa336a353a3bb10ea`
- Runner checkpoint: `3b8becab6b94899da71a28c8c0b4f96db9287159`
- Launcher checkpoint: `4a9bed911783179315e346664265e8380c8a393a`
- Runner revision: `cmp99-full-point-source-solution-cold-v1`
- Evidence payload SHA-256: `7AC158A8BD70ED01DE51C6E0F9B7810BD7B6DDCD5989FF9F1A11F48881FF8C2C`
- Evidence archive SHA-256: `6C4F76F6885A165D5A9DDB6373344C39A4800386E6267CF35A8C26ADD327294F`
- Executed notebook SHA-256: `38BDDA325F23E4838620CF136B835FD661B46B33E1A8AEF4A34334A75A358FF8`

The fresh Colab Pro+ CPU/high-RAM checkout verified the exact source, all four
source blobs, the Lean toolchain, the Mathlib pin and both textual guards. It
then stopped on the first compiler error in
`BalabanCMP99SourceFlatFullComplexPrecisionFibreAction.lean`: the attempted
`omit [NeZero d] [NeZero Nc]` on the arbitrary fixed-fibre action was false,
because its proof consumes the mode-action theorem carrying those instances.
The focal exited `1` after `1616.772 s`; no audit or downstream target ran.
This is FAIL evidence and does not retire any PRE-VALIDATION mark.
