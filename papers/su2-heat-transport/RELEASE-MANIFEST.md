# Task 48F release manifest — exact SU(2) algebraic all-mode intertwining

Frozen on 2026-08-04 for external audit.

## Git freeze

- Branch: `codex/48-su2-all-modes-paper`
- Frozen predecessor: Task 48E immutable body
  `3a1aee16b01d0ab3aa9c2279577b9b8e6bcb2d7d`
- Immutable Task 48F body commit (Lean, paper, PDF, verification log):
  `3b7bdda0219d778ddf65ee0966e1d94b038e8335`
- Earlier finite-witness SHA: `e6b672dda3e41da25a22178a7ef73ab8e7f8edb7`
- Exact satellite SHA: `05c4ec316cb9aa295416670a2578b1c2e77e1c36`
- Exact Mathlib SHA: `07642720480157414db592fa85b626dafb71355b`
- Integration policy: `origin/main` was fetched and already contained; no
  rebase, squash, or force-push was used.

The release commit containing this manifest is the branch tip reported by Git
and by the external handoff. The immutable body is the commit above, avoiding
a self-referential hash inside its own tree.

## What changed after the 5.08/10 critique

The predecessor proved an exact operator conjugacy only on
`span{chi_0, chi_1}`. This release adds one uniform Lean object for every
finite real character expansion:

- `AlgebraicModes := ℕ →₀ ℝ`, with no fixed mode cutoff;
- `characterLift` embeds those coefficients as concrete functions on bundled
  SU(2);
- exact Haar coefficient extraction proves that lift injective;
- exact Haar pairing identifies its finite-support coefficient geometry;
- the actual infinite-kernel heat operator intertwines that lift with the
  full diagonal Casimir step; and
- restricting the first two coordinates recovers the already frozen genuine
  SU(2)-inhabited two-state transport conjugacy and parent endpoint.

This closes the specific fixed-two-mode limitation at the algebraic level. It
does not silently promote that theorem to Peter–Weyl density, a completed
`L²(SU(2))` spectral theorem, non-class matrix coefficients, or a full-space
operator-norm result.

## Remote verification result

- `lake build YangMills.OS.SU2HeatAllModes`: `CLEAN48F_RC=0`
- All-mode `.olean`: materialized, 205240 bytes
- Source bytes: 13049
- Local and remote source SHA-256:
  `b85e633d7dd9910a415cc63f061d1f5d0f90ca12600f7fa65b9ce04528d3377e`
- Clean build window: `2026-08-04T20:16:11Z` to
  `2026-08-04T20:16:27Z` (16 seconds)
- `lake env lean papers/su2-heat-transport/Task48Axioms.lean`:
  `AXIOMS48F_RC=0`
- Axiom audit window: `2026-08-04T20:17:24Z` to
  `2026-08-04T20:18:18Z` (54 seconds)
- Printed axiom sets for all six new audited declarations:
  `[propext, Classical.choice, Quot.sound]`
- Project-local axioms / `sorryAx`: absent from every printed set

Execution was in Colab Pro+ CPU/high-RAM (50.99 GB), no GPU, on the visibly
confirmed account `lluiseriksson@gmail.com`. The fresh runtime was connected
at approximately 19:44 UTC. After the successful clean build and axiom audit,
disconnect-and-delete was selected and confirmed; the UI returned to the
disconnected “Reconnect” state at approximately 20:19 UTC.

## Hash capture method

Hashes are SHA-256. `raw` hashes exact working-tree bytes read with
`.NET File.ReadAllBytes`. For text files, `LF` decodes as UTF-8, maps CRLF and
bare CR to LF, encodes as UTF-8 without BOM, and hashes those bytes. `CRLF`
performs the same normalization and maps every LF to CRLF. This records both
transport-stable content and the Windows checkout form.

| File | Bytes | raw SHA-256 | LF SHA-256 | CRLF SHA-256 |
|---|---:|---|---|---|
| `YangMills/OS/SU2HeatAllModes.lean` | 13049 | `b85e633d7dd9910a415cc63f061d1f5d0f90ca12600f7fa65b9ce04528d3377e` | same as raw | `35e7da53a1c8d07c26b7ef184bd3d0df09ce715ff49d55061bc56171febbd684` |
| `YangMills/OS/SU2HeatIntertwining.lean` | 17500 | `000f7c2c9ec407aa5451dda115e1be3fe08749ff76e8493ee90754f34008905a` | same as raw | `ad3642e4afb2eaecda69296c84824dc9c328b3f1ae8867a3afc9e6feaeb80257` |
| `YangMills/OS/SU2HeatTransport.lean` | 11220 | `d86eb10d8bb104ce0419ee84466081def43d18b7bb85cbd68a38a365b051c931` | same as raw | `5201a4b2fb6c540a99e165b485b15eb47ee84063ab18265e562560fec3669657` |
| `papers/su2-heat-transport/Task48Axioms.lean` | 1392 | `8af6b665b194c487667360f10181f1441ffa803b588f4db61c3b87e5d278b85a` | same as raw | `b489e84707b20d13a29938df619ab80bd6c5d828c122e173626f3c7a5a1dcdec` |
| `papers/su2-heat-transport/su2_heat_transport.tex` | 25027 | `11bd3ffd3de1e348ef7754e781a13a7c4e5efb3ede0edc978e16f344d84ec828` | same as raw | `dad5bc239e4d21c1e5c33496c1bd4afcd37d38e20d57c0b3969ef05a7fa6eb46` |
| `papers/su2-heat-transport/README.md` | 954 | `96cf9350b2f52730e76468f183811e5329a9758da8c61e58062e4648459f95fd` | same as raw | `62b1eb394e3277a2eaabba772a79cb9b6738bf90980ae57b5eaebae0dabe5231` |
| `papers/su2-heat-transport/LEAN-VERIFICATION-LOG.txt` | 6074 | `3a1a15a16493a6348989ab5ad3df7afe3ce2c7f75d2aea95428f263cfe77fcbe` | same as raw | `fba645b28444973ca7da2420989740e01f52af60e4cc2f14aa3f0a77ce95885b` |

Binary artifact:

| File | Bytes | raw SHA-256 |
|---|---:|---|
| `output/pdf/su2_heat_all_modes_transport.pdf` | 388057 | `044796414e307856be687e7d18a6372a17b895ec794f93fe14d704f1bafbbdd5` |

The remote captures of the new Lean source and axiom driver matched the local
raw/LF hashes exactly.

## PDF QA

- TeX engine: MiKTeX pdfTeX 1.40.28
- Pages: 9, A4
- References and citations: resolved
- Undefined citations/references: none
- Overfull boxes: none
- Rendering: all nine final pages rendered at 120 dpi with Poppler
- Visual inspection: every final page inspected; no clipping, overlap, missing
  glyph, unreadable table, or broken equation was observed

## Attacks recorded for the external auditor

1. The finite carrier inhabits bundled SU(2): unitarity and determinant one
   remain proof fields of each state, not comments or numerical checks.
2. No eigenidentity, coefficient recovery, injectivity, pairing preservation,
   or intertwining conclusion is passed as a hypothesis.
3. The concrete normalized Haar measure, character orthogonality, integrability
   lemmas, dominated convergence, and infinite heat-kernel eigenidentity all
   participate in the proofs.
4. Non-vacuity is exact: Haar integration recovers every coefficient; on the
   finite quotient `(0,1)` maps to the proved nonzero sign vector.
5. The coefficient object contains all finitely supported modes and has no
   global cutoff, while the finite Dobrushin carrier is honestly retained only
   as the `{0,1}` quotient that connects to the published endpoint.
6. The finite covariance identity still derives the decay premise, and the
   projected transfer operator remains exactly nonzero.
7. No Python certificate participates in Lean; external tooling only rendered
   the completed PDF for visual QA.

This manifest freezes the object and the attempted attacks. It does not issue
the terminal external correctness, novelty, score, or publication-grade
verdict.
