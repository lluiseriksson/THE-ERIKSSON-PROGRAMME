# Task 48E release manifest — exact SU(2) two-mode intertwining

Frozen on 2026-08-04 for external audit.

## Git freeze

- Branch: `codex/48-su2-intertwining-paper`
- Frozen predecessor: `codex/48-su2-heat-paper`
- Predecessor SHA: `59c42d93ec5f4bf660792163c41407d9b1f3d8b4`
- Immutable body commit (Lean, paper, PDF, verification log):
  `3a1aee16b01d0ab3aa9c2279577b9b8e6bcb2d7d`
- Earlier finite-witness SHA: `e6b672dda3e41da25a22178a7ef73ab8e7f8edb7`
- Exact satellite SHA: `05c4ec316cb9aa295416670a2578b1c2e77e1c36`
- Exact Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- Integration policy: `origin/main` was fetched and already contained; no
  rebase, squash, or force-push was used.

The release commit containing this manifest is the branch tip reported by Git
and by the external handoff. The immutable body is the commit above, avoiding
a self-referential hash inside its own tree.

## What changed after the 4.78/10 critique

The predecessor paper only identified one equal scalar rate. This release adds
an operator-level bridge on the exact invariant sector `span{chi_0, chi_1}`:

- `continuousLift` is injective and preserves the exact Haar pairing;
- `finiteLift` is bijective onto the full finite Euclidean transfer space;
- actual infinite-kernel Haar convolution intertwines `continuousLift` with
  `diag(1, exp(-3t/4))`;
- the actual two-state transfer matrix intertwines `finiteLift` with the same
  diagonal operator; and
- the induced continuous-to-finite map is therefore an exact conjugacy on the
  specified sector, not merely an equality of rates.

No full completed-`L²(SU(2))` spectral theorem is claimed.

## Remote verification result

- `lake build YangMills.OS.SU2HeatIntertwining`: `BUILD48E_RC=0`
- Bridge `.olean`: materialized, 483824 bytes
- Source bytes: 17500
- Remote source SHA-256:
  `000f7c2c9ec407aa5451dda115e1be3fe08749ff76e8493ee90754f34008905a`
- Clean build window: `2026-08-04T17:47:28Z` to
  `2026-08-04T17:47:44Z` (16 seconds)
- `lake env lean papers/su2-heat-transport/Task48Axioms.lean`:
  `AXIOMS48E_RC=0`
- Axiom audit window: `2026-08-04T17:48:51Z` to
  `2026-08-04T17:49:16Z` (25 seconds)
- Printed axiom sets for all twelve audited theorems:
  `[propext, Classical.choice, Quot.sound]`
- Project-local axioms / `sorryAx`: absent from every printed set

Execution was in Colab Pro+ CPU/high-RAM (50.99 GB), no GPU, on the visibly
confirmed account `lluiseriksson@gmail.com`. The runtime was opened at
`2026-08-04T17:28:01Z`; after the successful module build and axiom audit,
disconnect-and-delete was selected and confirmed. The UI returned to the
disconnected “Reconnect” state.

## Hash capture method

Hashes are SHA-256. `raw` hashes the exact working-tree bytes read with
`.NET File.ReadAllBytes`. For text files, `LF` decodes as UTF-8, maps CRLF and
bare CR to LF, encodes as UTF-8 without BOM, and hashes those bytes. `CRLF`
performs the same normalization and maps each LF to CRLF. This records both
transport-stable content and the Windows checkout form.

| File | Bytes | raw SHA-256 | LF SHA-256 | CRLF SHA-256 |
|---|---:|---|---|---|
| `YangMills/OS/SU2HeatIntertwining.lean` | 17500 | `000f7c2c9ec407aa5451dda115e1be3fe08749ff76e8493ee90754f34008905a` | same as raw | `ad3642e4afb2eaecda69296c84824dc9c328b3f1ae8867a3afc9e6feaeb80257` |
| `YangMills/OS/SU2HeatTransport.lean` | 11220 | `d86eb10d8bb104ce0419ee84466081def43d18b7bb85cbd68a38a365b051c931` | same as raw | `5201a4b2fb6c540a99e165b485b15eb47ee84063ab18265e562560fec3669657` |
| `YangMills/OS/SU2TransportWitness.lean` | 11433 | `ff37b96303dcc02d66945173029a9dc2f8b5632fce98ffc02caa5fc4aa7dce8d` | same as raw | `65ce7cf819756e921630a8331bd53b5312367231a263f3b2de3521ae798cccfe` |
| `papers/su2-heat-transport/Task48Axioms.lean` | 940 | `a627b726859829e6ca48941143c0f3e339bad8923583db6147cbd9a81d090140` | same as raw | `84910dff94108d08fb9f327cc04e5c26e1d36227b7b2ec6b993636fbab5199db` |
| `papers/su2-heat-transport/su2_heat_transport.tex` | 23247 | `2a1b57a963dd30ce6a1e97b23264f0b15d06358efc45ab3fb16aaafdd5ec7fd2` | same as raw | `1827c331c835e3c214b5d677f0ecee3d559cb1b07012df242169cf1b2954d20f` |
| `papers/su2-heat-transport/README.md` | 781 | `64559edf4bc4611671808c9c385cdbbd5168febeca56a2f6447500345d66ed74` | same as raw | `d8fa6e7d3dcbf6e91a6b073de3d5029da9ffabca4f5366608a07f94b4a4bf7c6` |
| `papers/su2-heat-transport/LEAN-VERIFICATION-LOG.txt` | 3347 | `f1720ddf39b1829a69a0aa966305b6ba895668d421bf1517adadca84d14b78dd` | same as raw | `049ab9f8e3aaf2f3487d9eddc226e8c4210b4ef92da2f6898764b60c71be1895` |

Binary artifact:

| File | Bytes | raw SHA-256 |
|---|---:|---|
| `output/pdf/su2_heat_intertwining_transport.pdf` | 383225 | `deccc96e9d2f4c525f932f7ecbba5d1248bb262338ee469868b7f32298350a80` |

The remote capture of the new Lean source matched the local raw/LF hash
exactly.

## PDF QA

- TeX engine: MiKTeX pdfTeX 1.40.28
- Pages: 8, A4
- References and citations: resolved
- Undefined citations/references: none
- Overfull boxes: none
- Rendering: all eight final pages rendered at 1.5x with PyMuPDF 1.26.6
- Visual inspection: every final page inspected; no clipping, overlap, missing
  glyph, unreadable table, or broken equation was observed

## Attacks recorded for the external auditor

1. The finite carrier inhabits bundled SU(2): unitarity and determinant one
   are proof fields, not comments.
2. Neither intertwining identity is assumed; both are derived from concrete
   Haar integrals or exact two-state matrix entries.
3. The continuous lift is non-vacuous: exact Haar pairing gives coefficient
   norm, and evaluation at the phase/identity independently recovers both
   coefficients.
4. The finite lift is bijective and sends `(0,1)` to the exact nonzero sign
   vector.
5. The Dobrushin decay premise remains discharged by an exact covariance
   identity, and the projected operator remains exactly nonzero.
6. The scalar rate equality survives, but is now only one consequence of two
   operator commuting identities.
7. No Python certificate participates in the Lean proof; Python only rendered
   the completed PDF for visual QA.

This manifest freezes the object and the attempted attacks. It does not issue
the terminal external correctness, novelty, or publication-grade verdict.
