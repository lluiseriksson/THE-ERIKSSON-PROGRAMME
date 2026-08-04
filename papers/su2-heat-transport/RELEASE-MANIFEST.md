# Task 48 release manifest — exact SU(2) heat transport

Frozen on 2026-08-04 for external audit.

## Git freeze

- Branch: `codex/48-su2-heat-paper`
- Frozen predecessor: `codex/48-su2-exact-transport-witness`
- Predecessor SHA: `e6b672dda3e41da25a22178a7ef73ab8e7f8edb7`
- Body commit (Lean, paper, PDF, verification log):
  `b10b4fc9d5e7a1d748fabae8fc193e2d0da97ac2`
- Exact satellite SHA: `05c4ec316cb9aa295416670a2578b1c2e77e1c36`
- Exact Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- Integration policy: `origin/main` was fetched and already contained; no
  rebase, squash, or force-push was used.

The release commit containing this manifest is the branch tip reported by Git
and by the external handoff. The immutable body is the commit above, avoiding
a self-referential hash inside its own tree.

## Verification result

- `lake build YangMills.OS.SU2HeatTransport`: `BUILD48D_RC=0`
- `lake build YangMillsCore`: `ROOT48_RC=0`
- Axiom oracle: `AXIOMS48_RC=0`
- `sorryAx`: absent
- Printed axiom sets: `[propext, Classical.choice, Quot.sound]`
- Bridge `.olean`: materialized
- Root `.olean`: materialized

Execution was in Colab Pro+ CPU/high-RAM, no GPU, on the visibly confirmed
account `lluiseriksson@gmail.com`. The runtime was open from
`2026-08-04T15:41:40Z` to `2026-08-04T16:30:14Z` (48 minutes 34 seconds), after
which disconnect-and-delete was selected and confirmed.

## Hash capture method

Hashes are SHA-256. `raw` hashes the exact working-tree bytes read with
`.NET File.ReadAllBytes`. For text files, `LF` decodes as UTF-8, maps CRLF and
bare CR to LF, encodes as UTF-8 without BOM, and hashes those bytes. `CRLF`
performs the same normalization and then maps each LF to CRLF before hashing.
This records both transport-stable content and the Windows checkout form.

| File | Bytes | raw SHA-256 | LF SHA-256 | CRLF SHA-256 |
|---|---:|---|---|---|
| `YangMills/OS/SU2HeatTransport.lean` | 11220 | `d86eb10d8bb104ce0419ee84466081def43d18b7bb85cbd68a38a365b051c931` | `d86eb10d8bb104ce0419ee84466081def43d18b7bb85cbd68a38a365b051c931` | `5201a4b2fb6c540a99e165b485b15eb47ee84063ab18265e562560fec3669657` |
| `YangMills/OS/SU2TransportWitness.lean` | 11433 | `ff37b96303dcc02d66945173029a9dc2f8b5632fce98ffc02caa5fc4aa7dce8d` | `ff37b96303dcc02d66945173029a9dc2f8b5632fce98ffc02caa5fc4aa7dce8d` | `65ce7cf819756e921630a8331bd53b5312367231a263f3b2de3521ae798cccfe` |
| `lakefile.lean` | 1593 | `583592a6b0031ff69c049c7c1b8b7fe1fcf58013684fb0ec32c685e2b6afc1a7` | `befa599623f018ef30d370a9922c520f984a1b78109b71e5498b7eef52131ef7` | `a561fe1e2d9c5afa671e7d7fdaf06a508dc841372c7084192054176f54ce8962` |
| `lake-manifest.json` | 3601 | `e8f78d6ad89026e855bda34bc36e47a1ef1ad2cebeb7bdb2d1423fa7cb7f3118` | `bf3ee30c54a8b6554ac2baaa980c35e86146e7c127c26d773584c571b8efa6c1` | `9684f0988e883de5df592f5255cb12d1d501042b05008afbdc4ff378f95f88d4` |
| `YangMillsCore.lean` | 65184 | `b50e2d745ef27653c5c67373ad1454a172c40e3a566763da22d835ba768baebe` | `0aa2e49ec30963db9ad6f4d2116ee17531b63762b4cc7fe2e2c7e0c704d97c6d` | `5ae60b8f7614dd53b70986abebac562161fe58d4087c2c71cd77bbfc2049ca23` |
| `docs/SU2-HEAT-TRANSPORT-PAPER-CHARTER-20260804.md` | 3287 | `09f9ed6a0d83829e2ce618e5f6d187629a8bafb630f7ded14c7d0e032c625bea` | same as raw | `75b7037670e6376eb75bc8149a5fea891fae63f55e3ad981c76b9be6664ac449` |
| `papers/su2-heat-transport/Task48Axioms.lean` | 488 | `d7d601bce1bebae830dbe5dc8d16618b77573ddbc90c8b177c8145f7f196d757` | same as raw | `f70376eafc446f0ab71229259c1106c2dedd6fcdd806cadb0b8212970a6dab37` |
| `papers/su2-heat-transport/su2_heat_transport.tex` | 19450 | `33efaf3fdcbbd7f9ad039f1cf8c6ff4e3ccba523a8b0a4cc50bced9c43d84232` | same as raw | `fef50f266a587a8e549014477b6e366476afd13f9785238c86b55567dd354108` |
| `papers/su2-heat-transport/README.md` | 651 | `d52c11daf23cabdee0e2bec0ed5885f5e650dc31cc729c561e6fc639a1484927` | same as raw | `d37898fa043ee0b6dd7465970ee30fae48f25babd7e53d04c783fe1aef141890` |

Binary artifact:

| File | Bytes | raw SHA-256 |
|---|---:|---|
| `output/pdf/su2_heat_transport.pdf` | 370465 | `5b11361cf7495e7389ddd1a6558ede5b8853cadf1c6ae5f1e4a3d5e065762156` |

Remote capture matched the bridge source hash exactly. Remote log hashes are:

- module build: `af48ce7c8f3b4e91e29975ec1863505225dd810e4838e35a4a9fae082c05d7d2`
- root build: `36d8957602c4f22969b5b7b7894fa546ab2170c7cd3353c00cd278e72c59bf18`
- axiom oracle: `f8203de71560fcf9d2ef999502575e9900314da4441daeaf575cc1a20784d171`

## PDF QA

- TeX engine: MiKTeX pdfTeX 1.40.28
- Pages: 7, A4
- References and citations: resolved
- Undefined citations/references: none
- Rendering: all seven pages rendered at 1.5× with PyMuPDF 1.26.6
- Visual inspection: every page inspected; no clipping, overlap, missing glyph,
  unreadable table, or broken equation was observed

## Attacks recorded for the external auditor

1. The finite carrier inhabits bundled SU(2): unitarity and determinant one
   are proof fields, not comments.
2. The desired heat eigenidentity is not an assumption; it is derived by
   finite convolution orthogonality and dominated convergence.
3. The continuous eigenmode is nonzero because `chi_1(1)=2`.
4. The finite projected operator is nonzero by exact sign-vector evaluation.
5. The Dobrushin decay premise is discharged by an exact covariance identity.
6. The continuous and finite rates are proved equal to `exp(-3t/4)`.
7. No Python certificate participates in the Lean proof.

This manifest freezes the object and the attempted attacks. It does not issue
the terminal external correctness or novelty verdict.
