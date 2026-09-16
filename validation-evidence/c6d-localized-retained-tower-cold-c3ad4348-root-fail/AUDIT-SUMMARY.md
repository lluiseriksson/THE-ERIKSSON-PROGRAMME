# C6d localized retained tower — cold root failure

- Classification: `FAIL-FIRST-ROOT-ELABORATION`; the v1 gate is also
  superseded by the later 92-readout transitive coverage gate.
- Source SHA: `c3ad434890d8802a3d0b6ec5697862d488bba60f`.
- Runner revision: `c6d-localized-retained-tower-cold-v1`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Toolchain asset SHA-256:
  `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
- Focal: exit `0`, `1943.4068031149998` seconds.
- Focal audit: exit `0`, `21.817021334999936` seconds; its three readouts
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Root `YangMillsCore`: exit `1`, `10502.588823688999` seconds.
- Runner evidence marker:
  `a240040d7e267493da238f772297e0302e6b801843df4d0b74df5fd284bc183c`.
- Runner archive marker and verified downloaded archive SHA-256:
  `cb28384130f12913f157829b98f254a0d140a016d3bdfbf0e7325cbb6f6d499a`.

The first failed target was
`YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity`:

1. `BalabanCMP99Eq335PhysicalRetainedNearIdentity.lean:81:4` — failed to
   prove positivity/nonnegativity/nonzeroness.
2. `BalabanCMP99Eq335PhysicalRetainedNearIdentity.lean:136:15` — failed to
   synthesize `NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ)`.

The downloaded executed notebook contains `FINAL_STATUS=FAIL`, both evidence
markers, and the first failure exactly once.  No C6d PRE-VALIDATION mark is
removed and the terminal counters remain `20/41` and `TermSource = 0`.
