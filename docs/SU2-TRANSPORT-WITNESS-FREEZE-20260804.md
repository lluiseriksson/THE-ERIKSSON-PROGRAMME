# (48) Congelación para auditoría externa

## Identidad Git

- Rama: `codex/48-su2-exact-transport-witness`.
- Commit del cuerpo validado:
  `4a35e3299609d102f0535742305f38f6f8ecae9d`.
- Merge previo de `main`:
  `ac48ab798e8f4d8b93e5252319cdd0a881db1f8e`.
- Padres del merge:
  `c76b790505268eedcb8fe126bc399ccab82baa4f` y
  `04f87347f3e4d46a05e77bc1c70855794e111477`.

El commit del paquete que contiene este manifiesto se comunica junto al
objeto; no puede autorreferenciarse sin cambiar su propio SHA.

## Método de captura

Para cada ruta se resolvió `HEAD:<ruta>` y se leyó el blob con
`git cat-file blob <oid>` mediante
`System.Diagnostics.Process.RedirectStandardOutput` y `BaseStream`, sin
conversión textual del flujo Git. `lf_bytes` y `lf_sha256` pertenecen a esos
bytes canónicos. Para la variante CRLF, los bytes UTF-8 se decodificaron, se
normalizaron primero con `CRLF -> LF` y después con `LF -> CRLF`; se volvieron a
codificar como UTF-8 sin BOM y se midieron con SHA-256. Captura local-light,
un proceso Git por blob, 1.5 s totales.

## Blobs y hashes

| Ruta | Blob Git | LF bytes | SHA-256 LF | CRLF bytes | SHA-256 CRLF |
|---|---|---:|---|---:|---|
| `YangMills/OS/SU2TransportWitness.lean` | `1eca6de809b453978dd5e53f7be09ffad00572f3` | 11433 | `ff37b96303dcc02d66945173029a9dc2f8b5632fce98ffc02caa5fc4aa7dce8d` | 11713 | `65ce7cf819756e921630a8331bd53b5312367231a263f3b2de3521ae798cccfe` |
| `YangMillsCore.lean` | `1f1d942b103052a0c62114d820b1238c37f4da04` | 64096 | `eedea1b15ca0bf923b63e24aad8abd30a5f477c4edce2541a601bfde16b83be4` | 65160 | `c01c4ade3ac70ce3d2590994ffc5beff55f574fc39f96e4e10d3b0728f7ad726` |
| `docs/SU2-TRANSPORT-WITNESS-ORACLE.lean` | `36fe623ad2968cd81f63b9fd4b54258368f838cd` | 910 | `09b9d2828e7311fbc822e164985e08c2293baa884172296754a98d1a489690cf` | 925 | `f9016025a14ee896585895d91e5e36ff7fcab8e98007ca23ac457be255a802d9` |
| `oracle_check.lean` | `781598409161bc0c1a6db677cc3d68da48ee3f1f` | 235228 | `770923d37876192dbd6df462501e83146588a7a9187e511b7c4590489d6a46f0` | 238624 | `d478682c3f516044c1ead8ce421dd99211cf1b831fbe0d51a94cf6fb4dc22c22` |
| `docs/SU2-TRANSPORT-WITNESS-MAP-20260804.md` | `94bfa5c4609c4a6a100362aa728be15833278838` | 3982 | `b89a363446e4e33f71b42fab0bb21c6425c88a39b2c94558f37e4ec098275a7d` | 4064 | `bb4429f2829a3a9ab733c16d906eb2a50b5907966153533d3f13e6fa2a066b03` |
| `docs/SU2-TRANSPORT-WITNESS-COLAB-20260804.md` | `225d8a5fd62f49d0558175c9bb262e21a5092e1d` | 2979 | `d24b080e19b45bf08348bf98c13a54cee672be65922196794daae5af7a1583c7` | 3040 | `98c16472ce4d2c880fe9a6b874d30092e4dfcb46b21546972acb185f62b97177` |

## Estado de auditoría

La compilación y el oráculo son evidencia de fabricación, no un dictamen
terminal. El auditor debe verificar el commit del cuerpo, el commit del paquete,
los hashes anteriores, la salida Colab y los ataques enumerados en el informe
de validación.
