# F5 hot v1 — first-error diagnostic, not a seal

Draft source `4fd88ac8d04e12bf4751869802ca7ba23cad8acb`.
Runner `78b28c8ea106e94b3b9dba89d78f199d4f8b183c`.
Retained F4 source `5138e9bd4bc88797c91c21df5bb5c630c71600ca`.
Archive SHA256 `180ee030bd3dffda8dc964582e05bd1c4fa7b81b8cd7836b86657d636f5011ec` matched after download.

Mathlib-only reproduction: exit1, 6.990782669999135 seconds.
First error, verbatim:

```text
tmp/FullGreenFibreNormRepro.lean:23:33: error(lean.unknownIdentifier): Unknown constant `WithLp.toLp_apply`
```

Raw log SHA256 `04af69466ddf6047300b9c63d97916efe9641bb4146fe1bef18eadbedfb419cc`.
Stopped before the project prerequisite/draft queue. No F5 producer was
validated. Old bytes and exit code remain preserved; only the namespace
reference is corrected in source a289ee24dc41c25f2480c408de45b3105b09ce71.
Counters unchanged; `COLD_SEAL=0`.
