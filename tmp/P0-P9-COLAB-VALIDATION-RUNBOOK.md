# P0–P9 Colab validation runbook (prepared, not executed)

Status: **PRE-VALIDATION**.  This document prepares a single fresh-clone
intermediate-brick validation.  It is not compiler evidence.

## Immutable inputs

- Source checkpoint A7:
  `274d57089b3529e284525c167e7f75aeff0ce6e7`.  This PRE-VALIDATION commit
  contains the exact 39-file chain and its fail-closed static gates.
- Path-list SHA-256:
  `FEC594C0FBA52E14F8CC1E1BA886202FCDF2E425DE2C93E56DBF59FEEBB2FA61`
- Manifest SHA-256:
  `3874FF009D8BD409DE22D1E5B74BED38EF92237C594742352D228A29CF2F1945`
- P9 source SHA-256:
  `57D2EF9910DB7D548246AC0B4226CA8CBD97F29B17348BAEC9B70D499ACF34AA`
- P9 audit SHA-256:
  `EA3489E333FE66999EEBE1B949B157D07F93023D5F5A7B09FED558663EFDE37E`
- Static validator SHA-256:
  `D778C56620FD562985F6C0D2539D74B52104BFD30EE697138BD8453A8972C849`
- Static-gate self-test SHA-256:
  `445C6EEBBF0FE289716B0FB44C2A53105D9D4E507ACDEDFFA99FD9386E64E464`
- Runner checkpoint C8:
  `69095afc8f87cfbe0802eb9f60b80b378bcf3565`; runner Git-blob SHA-256
  `A9099BEBB613AF3B5380B6966587B21AB940476D1D8C81AF483EE64869DCC785`.
  It supersedes C7 after P2 exposed four independent elaboration defects;
  A7 repairs only those measured proof terms without changing statements or
  mathematical hypotheses.

## Runtime contract

1. Colab Pro+ CPU/high-RAM; no GPU.
2. Open the published one-cell notebook
   `scripts/colab_p0_p9_prefix_combes_thomas_validation.ipynb`.  Its launcher
   downloads runner checkpoint C8 over raw HTTPS and rejects any hash drift.
3. The runner clones exact source checkpoint A without credentials.  Verify
   detached `HEAD`, `lean-toolchain`, `lake-manifest.json`, Mathlib pin and all
   39 rows of `tmp/P0-P9-SCRATCH-MANIFEST.sha256` before elaboration.
4. Run `python scripts/check_lean_overlay_text.py --paths-from
   tmp/P0-P9-SCRATCH-PATHS.txt`, `python tmp/audit_p0_p9_diagnostic.py`, and
   `python tmp/test_p0_p9_diagnostic.py`.
5. Materialize the pinned dependency cache and then the exact nine-target
   tracked-project prerequisite frontier derived from direct `YangMills.*`
   imports in the 39-file list.  No manifest or toolchain drift is accepted.
6. For every non-audit source, execute `lake env lean PATH -o
   .lake/build/lib/lean/tmp/STEM.olean`; then execute its audit with `lake env
   lean PATH`.  Follow `tmp/P0-P9-SCRATCH-PATHS.txt` exactly and stop on the
   first nonzero exit code.  Do not jump directly to P7–P9: P0–P5 are semantic
   gates.
7. Record each command, duration and real child exit code.  For audit files,
   require one axiom header per expected declaration and reject `sorryAx`,
   `ofReduceBool` or any axiom outside `{propext, Classical.choice,
   Quot.sound}`.
8. Package transcript, hashes, environment and result JSON.  Disconnect and
   delete the runtime immediately after PASS or first FAIL.

## Superseded attempts

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

Runner C2 then materialized the exact nine-target prerequisite frontier
successfully (`8562` jobs, exit `0`) and reached the first mathematical file.
It stopped at `tmp/P0CanonicalPrefixTower.lean:136,159,185` because the
matrix operator-norm scope was not open.  Classification:
**FAIL-FIRST-ELABORATION**; no P0 declaration was accepted as verified.
The single executed notebook was preserved with SHA-256
`F13A4583CC994F561071F3C12211E5C745C5F35514DC5A5FA3B30D89DAD8B4CA`;
the remote structured evidence and archive hashes were respectively
`9CCEFB76F3A49F6D3B605F1AAB78EDB6941AA9BF9FA77EFEBDED6B9CE0171917`, and
`1AC7301AC46AE900EBFEDEB46E4EED6E1E34ACC9D9B4247A852029B8CFF7330B`.
The runtime was released automatically and the cell was not re-executed.

Runner C4 materialized the prerequisite frontier successfully (`8562` jobs,
exit `0`, `4718.921` seconds), wrote P0's scratch `.olean`, and then verified
P0 plus its ten-readout audit (`11.094` and `18.490` seconds, both exit `0`;
all readouts used only `propext`, `Classical.choice`, and `Quot.sound`).  The
queue stopped at P1: an addition congruence used the wrong orientation, the
base positivity proof assumed a non-definitional reduction, and `prefix` was
parsed as a reserved token.  Classification: **FAIL-P1-ELABORATION**.  P0 has
valid scratch compiler evidence but is not promoted or terminally sealed;
P1--P9 remain PRE-VALIDATION.  The executed notebook was preserved with
SHA-256
`20A1C26BD06120B7B7439C0C32673BC7C6775CDB9B2C9B19E7FC8F8322310E66`;
the remote structured evidence and archive hashes were respectively
`25091BE69E1EFB898CF4CEA3A4321858B1FFE334150D91B7E12868B9A4FEF7AB`, and
`A460DC52C9A2E463E9F1A917F3214237383A6058C9108246E4F569DE0E393F52`.
The runtime was released automatically and the cell was not re-executed.

Runner C5 materialized the prerequisite frontier successfully (`8562` jobs,
exit `0`, `3393.793` seconds), then verified P0 and its ten-readout audit
(`7.521` and `13.566` seconds, both exit `0`; only `propext`,
`Classical.choice`, and `Quot.sound`).  The repaired P1 stopped at one missing
imported declaration, `cmp99SourcePoincareEnergyCoeff_pos_succ`, at line 122;
classification: **FAIL-P1-IMPORT-FRONTIER**.  A5 copies no theorem and adds no
dependency: it derives the same depth-one positivity locally from the literal
coefficient definition and already imported nonnegativity lemmas.  The
executed notebook was preserved with SHA-256
`B3D0BF293B3CFBBCB85C09D6E990F2DE7DDA989704BFB83A7A5A93F610CE3760`;
the structured evidence and archive hashes were respectively
`3419080CABF56D527A42637CB42F45402A0342D23450FB3D9667A919324AB8B0`, and
`166184DACF09769655D236A4D57CCB00E911612BB3787CB673DD3B664453F190`.
The runtime was released automatically and the cell was not re-executed.

Runner C6 materialized the prerequisite frontier successfully (`8562` jobs,
exit `0`, `3461.301` seconds), then verified P0 and P1 with their audits
(`8.121`, `14.582`, `6.531`, and `10.275` seconds; all exit `0`).  P2 stopped
at lines 443/446 because an untyped `have hA := ...` left the implicit
`epsilon` underconstrained.  Classification: **FAIL-P2-ELABORATION**.  A6 pins
the literal energy-coefficient proposition and supplies `epsilon` explicitly;
the theorem statement and mathematical hypotheses are unchanged.  The
executed notebook was preserved with SHA-256
`BF341028FC6E0DD6A3BBE553CBE24399E397FB69328BECB8605D717D55B9D7E7`;
the structured evidence and archive hashes were respectively
`D39172E2C366153CF55AD38300E00BD23C3CFFBCD0E046FE1B3047954687E9F6`, and
`9CD651791D16FDB64A6F1C542D8AE5069BA9E17190E03A0A819311F558C0AB85`.
The runtime was released automatically and the cell was not re-executed.

Runner C7 again verified P0 and P1 with their audits, then reached four
independent elaboration defects in P2: a closed goal followed by `simp`, an
addition inequality supplied only with nonnegativity of its increment, an
attempt to rewrite the dependent ambient dimension while normalizing a scalar
power, and a `let`-bound operator passed to `rw` as though it were an equality.
Classification: **FAIL-P2-ELABORATION**; no P2 declaration is accepted as
verified.  A7 removes the redundant tactic, states the monotonicity step,
isolates the scalar power identity from all dimension-dependent types, and
unfolds the operator definition through `simpa`.  The executed notebook was
preserved with SHA-256
`E242C2D9ED94C160267774943EFD66959B7F7365996244F190F635296995AC54`;
the structured evidence and archive hashes were respectively
`EDE488B30F5CC684D2BAD58292B2460A8473E5EDFE0EE4DD4A9F2813C2AFA777`, and
`89BD84F623FD366A70B29846A249CD47AACFEA954F51E04B4E23B3E2A94C224A`.
The runtime was released automatically and the cell was not re-executed.

Runner C3 again materialized the exact prerequisite frontier successfully
(`8562` jobs, exit `0`, `5076.172` seconds).  P0 itself then elaborated with
exit `0` in `11.346` seconds.  Its audit stopped immediately because
`tmp.P0CanonicalPrefixTower` was not on the import path: the previous command
checked P0 without writing its `.olean`.  Classification:
**FAIL-SCRATCH-OLEAN-MATERIALIZATION**; P0 remains PRE-VALIDATION because its
axiom audit did not run.  The executed notebook was preserved with SHA-256
`D18751DA82354887F1B4878608E6B748773AC11E67F970E3852C9C05696157DE`;
the remote structured evidence and archive hashes were respectively
`140A176154F94C99DF8F7ABDC8F071E722FAE4B35B12E716EE4D58E2171ACB96`, and
`424BBCF22C983572D630539A4DE69AFB2AEF96069C66F2389AAA3E0E3A73170`.
The runtime was released automatically and the cell was not re-executed.

## Honest verdict boundary

A green run verifies only the 39-file scratch chain through the per-depth P9
Combes–Thomas statements.  It does **not** prove uniform CMP99 (3.42)
constants, the four source actions, C6c.4, window-15 attainment, any new
PreEq136 field, or a `TermSource` inhabitant.  Counters remain `20/41` and
`TermSource = 0`.
