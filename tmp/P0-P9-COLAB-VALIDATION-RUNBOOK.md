# P0–P9 Colab validation runbook (prepared, not executed)

Status: **PRE-VALIDATION**.  This document prepares a single fresh-clone
intermediate-brick validation.  It is not compiler evidence.

## Immutable inputs

- Source checkpoint A:
  `fecf2f768f049b59743a6b2df8a7d569748254c1`.  This PRE-VALIDATION commit
  contains the exact 39-file chain and its fail-closed static gates.
- Path-list SHA-256:
  `FEC594C0FBA52E14F8CC1E1BA886202FCDF2E425DE2C93E56DBF59FEEBB2FA61`
- Manifest SHA-256:
  `D5B829CB109E8062A19B9F57A9A9A7346170652D51582F05AC731636595C9325`
- P9 source SHA-256:
  `57D2EF9910DB7D548246AC0B4226CA8CBD97F29B17348BAEC9B70D499ACF34AA`
- P9 audit SHA-256:
  `EA3489E333FE66999EEBE1B949B157D07F93023D5F5A7B09FED558663EFDE37E`
- Static validator SHA-256:
  `C60B7C62CCA3BC6CCFE3F5B8939F8903A7DBEA7DE213BD5C6084A9194D38D84D`
- Static-gate self-test SHA-256:
  `445C6EEBBF0FE289716B0FB44C2A53105D9D4E507ACDEDFFA99FD9386E64E464`
- Runner checkpoint C2:
  `89ddfe78cb4348cff4ea0b87a5e5344622e7c709`; runner Git-blob SHA-256
  `1C607BAC9523D60CAFC53770F933997FCD7C4559E15EC7E05B69FD88D714EDDA`.
  It supersedes checkpoint C
  `29139afded5f10653deef05b632d61f571433eb7`, which omitted the local
  `YangMills` prerequisite frontier from a fresh clone.

## Runtime contract

1. Colab Pro+ CPU/high-RAM; no GPU.
2. Open the published one-cell notebook
   `scripts/colab_p0_p9_prefix_combes_thomas_validation.ipynb`.  Its launcher
   downloads runner checkpoint C2 over raw HTTPS and rejects any hash drift.
3. The runner clones exact source checkpoint A without credentials.  Verify
   detached `HEAD`, `lean-toolchain`, `lake-manifest.json`, Mathlib pin and all
   39 rows of `tmp/P0-P9-SCRATCH-MANIFEST.sha256` before elaboration.
4. Run `python scripts/check_lean_overlay_text.py --paths-from
   tmp/P0-P9-SCRATCH-PATHS.txt`, `python tmp/audit_p0_p9_diagnostic.py`, and
   `python tmp/test_p0_p9_diagnostic.py`.
5. Materialize the pinned dependency cache and then the exact nine-target
   tracked-project prerequisite frontier derived from direct `YangMills.*`
   imports in the 39-file list.  No manifest or toolchain drift is accepted.
6. Execute `lake env lean PATH` for every nonblank path in
   `tmp/P0-P9-SCRATCH-PATHS.txt`, in listed order, stop on the first nonzero
   exit code.  Do not jump directly to P7–P9: P0–P5 are semantic gates.
7. Record each command, duration and real child exit code.  For audit files,
   require one axiom header per expected declaration and reject `sorryAx`,
   `ofReduceBool` or any axiom outside `{propext, Classical.choice,
   Quot.sound}`.
8. Package transcript, hashes, environment and result JSON.  Disconnect and
   delete the runtime immediately after PASS or first FAIL.

## Superseded instrumentation attempt

The first execution of runner C reached all transport, pin, cache and static
gates, then stopped before mathematical elaboration at
`p0_p9_01_p0canonicalprefixtower`: Lean reported `unknown module prefix
'YangMills'`.  Classification: **BLOCKED-PREREQUISITE-MATERIALIZATION**;
P0--P9 remain not compiler-verified.  The runtime was released and the cell
was not re-executed.

- structured evidence SHA-256:
  `20BF41FFB98EE633FBE72577CCDF37DB9ECBC1E517773AAAC8B4976B97BDF6B9`
- Colab evidence archive SHA-256:
  `C6C20A3F331BF2C98C640F55253107FF6198EAB3184F241B7455DF20FFCB1C6E`
- downloaded executed-notebook SHA-256:
  `A0E1706AE914654DC47EDC9A213602F4BAEB77D38BD7B6B366391DC733369232`

## Honest verdict boundary

A green run verifies only the 39-file scratch chain through the per-depth P9
Combes–Thomas statements.  It does **not** prove uniform CMP99 (3.42)
constants, the four source actions, C6c.4, window-15 attainment, any new
PreEq136 field, or a `TermSource` inhabitant.  Counters remain `20/41` and
`TermSource = 0`.
