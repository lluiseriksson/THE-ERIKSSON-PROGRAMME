# CMP99 full point-source dictionaries cold seal

- Source checkpoint: `ea72912edf9fd40121589ed89854a9bc9ebf02bb`
- Runner revision: `full-point-source-character-dictionaries-cold-v1`
- Runtime: Colab Pro+ CPU/high RAM
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`
- Lean toolchain asset SHA-256:
  `BF3E0A4025E47A0BEA9ED907D12DCCD3D3590B1D8AD6C55A915298B01AD9D3E`
- Status: `PASS`
- Final focal graph: `8716/8716`
- Audited declarations: 8, each within
  `{propext, Classical.choice, Quot.sound}`
- Colab payload SHA-256 (without the file's final newline):
  `D8AD7E67E686D6F5C9EA97C01813C245D4A42F8D18FF468B1151FCAA362EF73C`
- Extracted `evidence.json` SHA-256 (including its final newline):
  `5230A7D2503DCDD41D3C3111234F26D998442CE8BB30D1CFFC10C02527B52202`
- Downloaded archive SHA-256, rechecked on Windows:
  `2700E766328B1095960EB254F041C2ACF6723D553E633C2E974341D288AAC2E2`

This seals only the source-character, target-character, one-fibre integrand
and reflected outer-synthesis dictionaries.  It does not close the full
Eq. (2.46) centered-to-physical sample transport, finite-grid aliasing to the
generated regional Green, CMP89 (2.42), a uniform physical `B0`/`delta0`,
window 15, any terminal field, or `TermSource`.
