# P0–P9 Colab validation runbook (prepared, not executed)

Status: **PRE-VALIDATION**.  This document prepares a single fresh-clone
intermediate-brick validation.  It is not compiler evidence.

## Immutable inputs

- Source checkpoint A16:
  `c537ea3babcc1770570f9a131e11e8f11d6806ba`.  This PRE-VALIDATION commit
  contains the exact 39-file chain, its fail-closed static gates, and one
  Mathlib-only P2b algebra reproducer executed before project materialization.
- Path-list SHA-256:
  `FEC594C0FBA52E14F8CC1E1BA886202FCDF2E425DE2C93E56DBF59FEEBB2FA61`
- Manifest SHA-256:
  `7DC25B62AC67F3C6C55866B3BF32D70C55C964CCC0C13DAFFE07B7DCAFFF72BD`
- P2b algebra reproducer Git-blob SHA-256:
  `6B0B71190CF629A3BAC9E1D2F8FFE24C0FFCF157573BCBCAA5C6D8507D25764E`
- P9 source SHA-256:
  `57D2EF9910DB7D548246AC0B4226CA8CBD97F29B17348BAEC9B70D499ACF34AA`
- P9 audit SHA-256:
  `EA3489E333FE66999EEBE1B949B157D07F93023D5F5A7B09FED558663EFDE37E`
- Static validator SHA-256:
  `A1139CFED4574E34FC80F25CE43640E4F9D4A868A15300D87C5C5C5CC0F28A34`
- Static-gate self-test SHA-256:
  `445C6EEBBF0FE289716B0FB44C2A53105D9D4E507ACDEDFFA99FD9386E64E464`
- Runner checkpoint C19:
  `36ba21f54844079971994fc0b3e67bcd19e8597c`; runner Git-blob SHA-256
  `93E72530731986C234BE2421CD0270DBDD16E486665A56D5A72EADCAEB319981`.
  It supersedes C18 after C18 retained the exact P2c failure: three local
  abbreviations were referenced outside the theorem-statement `let` scope.
  A16 recreates those exact abbreviations inside the proof without changing
  the equality, hypotheses or constants.  C19 preserves
  every child's complete combined output as a hash-checked stage log inside
  the evidence archive and requests its browser download before runtime
  release.  The immutable mathematical source is A16; no theorem
  statement, hypothesis, axiom contract, target or prerequisite is changed.

## Runtime contract

1. Colab Pro+ CPU/high-RAM; no GPU.
2. Open the published one-cell notebook
   `scripts/colab_p0_p9_prefix_combes_thomas_validation.ipynb`.  Its launcher
   downloads runner checkpoint C19 over raw HTTPS and rejects any hash drift.
3. The runner clones exact source checkpoint A without credentials.  Verify
   detached `HEAD`, `lean-toolchain`, `lake-manifest.json`, Mathlib pin and all
   39 rows of `tmp/P0-P9-SCRATCH-MANIFEST.sha256` plus the separately bound
   P2b reproducer before elaboration.
4. Run `python scripts/check_lean_overlay_text.py --paths-from
   tmp/P0-P9-SCRATCH-PATHS.txt`, `python tmp/audit_p0_p9_diagnostic.py`, and
   `python tmp/test_p0_p9_diagnostic.py`.
5. Execute the P2b Mathlib-only reproducer.  Only if it exits `0`, materialize
   the exact four-target P0--P5
   prerequisite frontier.  Immediately before P7, materialize the remaining
   five direct-import targets.  Together these are the same exact nine-target
   frontier; the split only makes an early failure observable without first
   compiling dependencies used solely by P7--P9.  No manifest or toolchain
   drift is accepted.
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

Runner C8 materialized the full prerequisite frontier (`8562` jobs, exit `0`,
`4857.122` seconds), then verified P0 and P1 with their audits (all four exits
`0`).  P2 stopped at line 251 on one scalar identity: rewriting the dimension
also rewrote the subtracted exponent on the target side.  Classification:
**FAIL-P2-ELABORATION**; P2 remains PRE-VALIDATION.  A8 replaces that broad
rewrite by a directed `calc` step that changes only the intended power.  The
executed notebook was preserved with SHA-256
`AAAD8F18566ADDEDC81D264240CB2D717A80B596284CD42FD533C2A0CE927E49`;
the structured evidence and archive hashes were respectively
`F198C375CA6CCD5BDD418A4D4188DF72E6DCE7CF524F4B79088E8EEE9727EE07`, and
`917043F54D7088213DB5AACA0BC33B02A85B4E82E4188F71C1D3A1EF37E299B0`.
The runtime was released automatically and the cell was not re-executed.

Runner C9 split prerequisite materialization and built the four-target
P0--P5 frontier successfully (`8539` jobs, exit `0`, `1450.986` seconds).
P0, P1 and P2 sources all elaborated with exit `0`; their audits also exited
`0` and printed only the allowed axiom trio, with one P2 declaration printing
the strictly stronger empty-axiom form.  The runner then classified the P2
audit as failed because its inherited parser counted the 25 nonempty lists
but not that one empty list against the expected total of 26.  Classification:
**BLOCKED-AXIOM-PARSER** after successful Lean elaboration; the complete
P0--P9 chain remains PRE-VALIDATION.  C10 repairs only this instrumentation
defect and keeps the expected total at 26.  The executed notebook was
preserved with SHA-256
`335F67D4EE4A967BE87DE0882EC26DEA7C4BA2784E6C66077AEF464900CFF065`;
the structured evidence and archive hashes were respectively
`80957B9923677EA2CD9E481E05B97842C2C5B47CAE4D39261BA14375146E9837`, and
`15429C1654BC03D3BDA75A95D250E8FC4BF8F72A2650D1663EA0E92CFB482BC6`.
The runtime was released automatically and the cell was not re-executed.

Runner C10 verified P0, P1 and P2 sources and all three audits.  The P2 audit
was accepted with 26 exact headers: 25 used only the allowed trio and one was
axiom-free.  The queue then stopped in P2b on four measured elaboration
defects: a simplifier call after definitional reduction, two structural
composition rewrites applied before beta reduction, and one `let`-bound
operator supplied to `rw` as if it were an equality.  Classification:
**FAIL-P2B-ELABORATION**; P2b--P9 remain PRE-VALIDATION.  A9 replaces only
those proof-shape steps with directed `change`/`simpa` normalization.  The
executed notebook was preserved with SHA-256
`678D53C5FF7F066468383A09137D8A301BC123426C5CB36BAD2FAED53B4D4F5F`;
the structured evidence and archive hashes were respectively
`41B89D56AD89D8467127B2DF099308C7F0BC0E80720F7F8CD90BBED952DE7421`, and
`F8C2DBEB49DC673BA42D3468999540168D23BE7332CE6DFBD3452D0970307A64`.
The runtime was released automatically and the cell was not re-executed.

Runner C11 again verified P0, P1 and P2 sources and all three audits after a
cold four-target prerequisite frontier (`8539` jobs, exit `0`, `2333.845`
seconds).  P2b then stopped on three proof-shape errors that mention no project
object: expansion of a continuous-linear-map application under an inner
product, separation of target-only linearity from the inverse-law point
identity, and a redundant directed inner-product rewrite after scalar
normalization.  Classification: **FAIL-P2B-GENERIC-CLM-ALGEBRA**; P2b--P9
remain PRE-VALIDATION.  A10 changes no theorem statement or hypothesis and
adds a Mathlib-only reproducer so this class is checked before the next cold
project bootstrap.  The executed notebook was preserved with SHA-256
`78B196C90A629BB812D5BA81BD93647839A32A9DAD481BFE610DBE89517FD070`;
the structured evidence and archive hashes were respectively
`B0E6584AFABD9D082CD601DC2AB646C7D6510F47F5A9220AA17A4F1AC5AF3406`, and
`36A3C6174F9FD7E42BA4F684E55E35E9166603FFB177C386ED6B5A1451DA6798`.
The runtime was released automatically and the cell was not re-executed.

Runner C12 verified the exact A10 transport, toolchain and all 40 blob hashes,
then stopped in the textual overlay gate after `28.904` seconds: the new
Mathlib-only reproducer opened a `noncomputable section` without its terminal
`end`.  No Lean command and no project materialization ran.  Classification:
**BLOCKED-TEXT-GUARD**; the mathematical status is unchanged.  A11 adds only
the missing section terminator, and the same local guard now accepts the
one-file delta.  The executed notebook was preserved with SHA-256
`9642BFF326BB064AD0A31548E3603D2D4DFC786983CBEC5FA3AB58B03654E028`;
the structured evidence and archive hashes were respectively
`AFE6963785F0A3639E6C099C18C7899F6FA70EE2619510FA407704FAD73CBD8C`, and
`54A01F8E201685009E9C6AB5D97BA8728D45A1E40AF4A554188C6EA69BDED04E`.
The runtime was released automatically and the cell was not re-executed.

Runner C13 verified A11, both textual gates, the exact Mathlib pin and the
static source contract.  Its Mathlib-only reproducer ran in `18.550` seconds:
the symmetry and Euler proofs compiled, and the completed-square proof stopped
on one redundant `inner_sub_left` rewrite after the target had already exposed
only right-hand subtractions.  No YangMills prerequisite was materialized.
Classification: **FAIL-P2B-MINIMAL-REPRO**; the mathematical scope is reduced
to one generic normalization and P2b--P9 remain PRE-VALIDATION.  The executed
notebook was preserved with SHA-256
`4D6B86ECDF73261A1DFB1425230C25F2F457A30DABF4D51022C065728DDA3D53`;
the structured evidence and archive hashes were respectively
`3A0F021933ACAB9F815C314F7779560CFE999439D848F82825A1B2D20A04074B`, and
`859FCE0F24F074DD213E64290943588B33FD812C8EEE5F922A3207005B30041A`.
The runtime was released automatically and the cell was not re-executed.

Runner C14 verified A12 and reached the same minimal reproducer in `21.724`
seconds.  All rewrites then succeeded; `ring` left one goal whose only
non-algebraic distinction was the order of a real inner product,
`inner eta q` versus `inner q eta`.  No YangMills prerequisite was
materialized.  Classification: **FAIL-P2B-REAL-INNER-SYMMETRY**; A13 adds the
single explicit `real_inner_comm` instance before normalization.  The executed
notebook was preserved with SHA-256
`10602FBC56D462CDBE7AA3170A5E3B10A41F2F6EF3B3D3FF84ADFBA2851DA919`;
the structured evidence and archive hashes were respectively
`0B70B7C472DC146D9A235ADA3ED4810585FA6D8B98B9426FA2BCE584BF54330E`, and
`F03A33872EA3F2B2E774ADF9EF5EE821A9C1CE34917225D12B959CA254C9F995`.
The runtime was released automatically and the cell was not re-executed.

Runner C15 verified A13 and reached the minimal reproducer in `14.677`
seconds.  The explicit real-inner symmetry compiled, but the final `ring`
goal retained the left subtraction and scalar actions inside four inner
products.  No YangMills prerequisite was materialized.  Classification:
**FAIL-P2B-INNER-LINEARITY-NORMALIZATION**; A14 expands only those generic
inner-product operations before field normalization.  The executed notebook
was preserved with SHA-256
`5C3AC8FDBADF2B692D637EEB2ADBE6C65E3C1B5F5034C3963A192DAEC86C98FB`;
the structured evidence and archive hashes were respectively
`FCC915EBAD4A7D037947183874D6A559BD8F2202B33386C5F89D59FE2D470CD9`, and
`6E4E4C2267A53ECCA33A3BCB4A5FD52CBFA1E8E9F4656CD7FC2178EEC24FC263`.
The runtime was released automatically and the cell was not re-executed.

The first C16 connection received only `12.67` GiB of RAM and was rejected
before checkout or Lean.  Classification: **BLOCKED-HIGH-RAM**.  The executed
notebook was preserved with SHA-256
`68A2509F3DB323F336B34DE4771FC79D05728D5CCA808BAD7EACD59A7B3ADF4C`;
the structured evidence and archive hashes were respectively
`E5A40E3E2F4652B4E169447D5F045CE4E86E3C66765283AC40DE741112E049C2`, and
`B24C7438463CCFDE92312FA2704F911B9F50240D2FA37AE95D01F52EDC43B3CD`.

Runner C16 then ran on a verified `50.99` GiB high-RAM runtime.  The minimal
reproducer passed in `35.443` seconds, the cold `8539`-job prerequisite build
passed, and P0, P1, P2 and P2b plus all four audits passed with only the
allowed axiom set.  P2c stopped on six measured elaboration defects: obsolete
`Fin` normalization names, duplicate norm instances, three uninferred scalar
parameters, an opaque `currentPrefix` carrier equality, and a `let`-bound
operator supplied to `rw`.  Classification: **FAIL-P2C-ELABORATION**; P2c--P9
remain PRE-VALIDATION.  A15 repairs exactly those defects and propagates the
same already-measured `Fin` compatibility spelling through P3--P4.  The
executed notebook was preserved with SHA-256
`E7C2E38C67FE788006EB754F980335BCE2C764A934654AB218924DCABC9033F9`;
the structured evidence and archive hashes were respectively
`8D53BE70D55154E4420B1AE699340DDF5A050EC2BC2AC63407A62A5D7ED04952`, and
`FA44C863B879CBE028009D99B93AF072DD695B7D2C43A0EC9F65A734AB04D0A1`.
The runtime was released automatically and the cell was not re-executed.

Runner C17 ran A15 on the same verified `50.99` GiB high-RAM class.  The P2b
reproducer passed in `67.870` seconds, the cold prerequisite frontier passed
in `1787.416` seconds, and P0, P1, P2 and P2b plus all four audits again exited
`0`.  P2c was the first failing stage, with exit `1` after `15.348` seconds and
output SHA-256
`6B00C2D02819D4C08939D985BDCBEC078A9BA1C19D917FA926F0FBB3C4C8F38E`.
The released runtime's archive had SHA-256
`660D20769B324E15659F1E0045238053566CDA77084639589B3FC160BC513D15`;
the recovered structured evidence has SHA-256
`6208F059275288DD0F333BE7CDECA32C9A15C33A9610211A58420976F8A628F2`.
Its recovery notebook is retained under
`validation-evidence/p0-p9-colab-fail-p2c-a15-recovered/` with SHA-256
`8E790BAFCEA8E7449C6B18BC1B3601356026B535BD4B0C663C2AFC63552CADE8`.
Classification: **FAIL-P2C-ELABORATION / INCOMPLETE-DIAGNOSTIC-RETENTION**.
The exact P2c diagnostic lines were not retained, so no mathematical source
change is inferred from this run.  C18 fixes only that evidence-retention
defect and reruns the same immutable A15 queue stop-on-first-error.

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
