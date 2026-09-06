# R1 evidence, 6 September 2026

The [campaign plan](../../PHYSICAL-REFLECTION-PLAN.md) is the status authority.
The [task-owned Colab notebook](https://colab.research.google.com/drive/1Hj6-16RKQ8Fk1gzEfJC6Qg5aqmVJKjaw)
preserves executable source, command outputs, manifests and lossless Base64
exports of the evidence archives. It may require the owner's Google access;
the small public transcripts in this directory do not depend on that access.

## Initial diagnostic (superseded source, retained evidence)

Base `23f488959005718ac634176d02f5626e8ce70151` plus UTF-8/LF source SHA-256
`1046B1EF184A1940A965AC9DFE0B3F65C30140083FC83EC6DBC8D5824084FCA4`.
`lake build YangMills.L0_Lattice.GaugeConfigurations` passed at 8159 jobs;
`lake build YangMills.OS.PhysicalWilsonSquare` passed at 8160 jobs;
`lake env lean R1Audit.lean` passed for all ten listed headlines. No full
`YangMillsCore` build was performed by this initial diagnostic.

`initial-oracle.txt` is the verbatim oracle stdout, transcribed from the
notebook and checked against the Colab-recorded SHA-256 of its original
UTF-8/LF bytes:
`a9682979f999560fb5ba9cd40422252aaf75657bd859a55cabbd6f99476fb685`.

The complete archive contains the original draft, oracle source, every stage's
complete command log and the manifest. Archive byte SHA-256:
`47aa60230ec74bf11b5e036ddb4fa0e19dc196164843d61ee6d6fdf18c50ff32`;
size 6551 bytes. The notebook's second cell output preserves those exact
bytes as Base64; decoding is a transport operation, not another proof run.

The later removal of redundant gauge covariance changes the source and the
headline count. This ten-headline transcript must not certify the revised
nine-headline source. R1 supplies local geometry; R2–R5 remain separate.

## Revised R1 scoped check

The fresh revised-source execution uses base
`5066f3de44af98d73dc23e1062a0bcaf75b3a7e4`, with source UTF-8/LF SHA-256
`21A09C1447E2291C3D46679AAD76387794C4C95A3D4B13FF3A59CCDB47923921`
and the full oracle overlay UTF-8/LF SHA-256
`D67DDFC964D29FF30AA670618F9FF93F2E19EE02701BD79263917D79A1EFE141`.

Observed successful commands: unchanged core build (8466 jobs), focal R1
build (8160 jobs), nine-declaration `R1Audit.lean`, source consistency,
dashboard validation and the complete oracle import set (8467 jobs).
`revised-oracle.txt` is the verbatim nine-declaration output observed in that
execution. Its UTF-8/LF SHA-256, now matched to the final Colab manifest, is
`18765288B1B3A26D9B7E8FC0877A2447F4DA578961ACECF8030AA2BF57D5EA17`;
the executable focal oracle is retained as `R1Audit.lean`.

The full oracle also exited **0**, with **2815** readouts, including **26**
axiom-free declarations. Every dependency is within the standard allowed set.
The complete stdout hash is
`bf173c24b55930b876a4a77ae34347bfe2d3644b3a16798cec048a5b686f1a21`.
`revised-manifest.json` transcribes the final manifest's data, preserving all
commands, real exits, timings, source/log hashes and the scoped verdict; its
JSON whitespace differs from the archived original and no byte identity of
those two JSON serializations is claimed.

The final notebook output preserves the complete revised archive as lossless
Base64, SHA-256
`0ffc58c188fdb8fad88a3f5c930d1bbb3920ee6857dbecab7cc820477941c330`.
It contains all complete logs and source overlays. This archive has not been
downloaded into the public repository; do not mistake printed log tails for
the complete logs. The public transcript and manifest expose the focal
results and the global check's provenance without requiring Google access.

Execution: `08:09:53.593994Z`–`08:51:29.847037Z`, **2496.253 s** on this task's
CPU/high-RAM runtime. Automatic release followed evidence preservation; the
disconnected UI was observed before `08:52:28Z`. Exact allocation and billing
times were not captured. No runtime is left connected for this unit.

The two production/global-oracle overlays are the new standalone module and
`oracle_check.lean`; all other production Lean modules are unchanged from
the base. The generated focal driver is additionally preserved in this
documentation directory as `R1Audit.lean`.
No R1 core-root import was added. One fresh revised run and the earlier
different-source diagnostic are not two terminal reproductions at one SHA.
