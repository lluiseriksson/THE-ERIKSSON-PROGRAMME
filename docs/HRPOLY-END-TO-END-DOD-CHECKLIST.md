# hRpoly end-to-end Definition-of-Done checklist

Status: LIVE COMPLETION AUDIT.  This document prevents a green intermediate
brick from being reported as closure of hRpoly.  A row is complete only when
the cited current-state evidence proves the full scope of that row.

Baseline: `9da8a6feaf832067c45e64398c77fbb61314f225` is an ancestor of the
active branch.  Branch: `codex/cmp116-interacting-wilson-hessian`.  PR #29
must remain draft until every row below is complete.

Hard invariants while this checklist is open:

- terminal producer count is `20/41`;
- `TermSource = 0`;
- window 15 is compatible but not attained.

These values may change only when a compiled source-facing producer or
inhabitant justifies the exact movement.

| requirement | status | authoritative evidence / remaining gate |
|---|---|---|
| Exact baseline ancestry | **complete** | `git merge-base --is-ancestor 9da8a6fe... HEAD` returned success on 2026-08-25. |
| Source-specific Units A--E | **complete** | Cold run `32329127991`, source `9d378412...`, 36/36 stages exit zero, 124 allowed axiom blocks, inner SHA-256 `90D66229...`, outer SHA-256 `1E500200...`; ledger Addendum 869. |
| Unit F periodic-owner continuation | **complete** | Cold run `32343215395`, source `fa29c350...`, 8/8 stages exit zero, 49 allowed axiom blocks; ledger Addendum 870. |
| C6 source/localized retained dependency boundary | **in progress** | Exact Colab v8 gate at source `e44b164c...`; no seal until literal `FINAL_STATUS=PASS`, downloaded notebook, 92-readout post-verifier and exact 34-file marker retirement. |
| C6d.1 literal localized retained precision | **open** | Six-file, eleven-declaration queue prepared.  It must construct the regional `Delta'_a = Delta_U + a_j Q'^* Q'` from the physical regularity witness and the internally generated retained tower, with the two summands and source spacing visible; no free precision, `Qprime`, coercivity estimate, Green operator or second spacing is admissible. |
| Eq. (3.37) complex Ubar boundary | **open** | Fourteen-file cold gate prepared.  Promotion requires its own evidence package; no compiler verdict yet. |
| Complex inverse and all-orientation small-field producer | **open** | PRE-VALIDATION prerequisite gate prepared.  It must prove the explicit `(1+r)^M` costs, `q/(1-q)` inverse loss and the joint zero-radius non-vacuity witness. |
| Forced finite complex recursion | **open** | Must construct every background internally from literal `U`, `A`, `eta` and a scalar flowing-radius chain.  No background family, free `hdev`, per-scale smallness proof or terminal equality may be an input. |
| Uniform physical `B0, delta0` and retained-tower transport | **open** | Fixed-depth/source-flow pieces are sealed; the uniform retained-tower producer is not. |
| Physical window 15 | **open** | Compatibility is proved; attainment requires the literal regional defect/Neumann estimate, not a renamed `norm R' < 1` hypothesis. |
| `PreEq136` producers | **open: 20/41** | Every remaining row must have a source-facing producer.  Assemblers do not increment the numerator. |
| First conditional `TermSource` inhabitant | **open: 0** | Requires `41/41`; a constructor receiving `PreEq136` is not an inhabitant. |
| Lemma-1 equation (1.36) for the physical operator | **open** | Generic L1/L2 and substantial source substrate exist, but the printed physical L1--L9 chain and final bound are not fully discharged.  This obligation is outside the 41-row conditional constructor. |
| Unconditional `TermSource` inhabitant | **open** | Requires the physical Lemma-1 certificate, not a free residual bound. |
| `hraw -> H# -> hprofile` physical chain | **open** | Exponential profile cannot remain a final hypothesis. |
| Nontrivial terminal theorem application | **open** | No terminal application exists yet. |
| Full clean build and complete axiom oracle | **open for final SHA** | Intermediate cold seals do not substitute for the terminal repository-wide build/oracle. |
| Terminal reproducibility | **open** | Two independent fresh heavy-environment checkouts at the same final SHA, with separate build state and matching output hashes. |
| Final paper | **open** | Compile, render and verify the final paper against the sealed theorem graph; no stale counters, placeholders or claims beyond compiled evidence. |
| PR #29 governance | **in progress** | PR is draft and tracks the active branch.  Keep draft until the full checklist is complete; use fast-forward publication only. |

Completion is forbidden while any row is open, while any source module still
contains a live PRE-VALIDATION notice that the final claim consumes, or while
an input merely renames an obligation listed above.
