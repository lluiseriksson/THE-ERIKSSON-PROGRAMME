# Physical Wilson cylinder R2 evidence

All proof execution uses the task-owned CPU/high-RAM Colab notebook:
[R1/R2 source and complete evidence archives](https://colab.research.google.com/drive/1Hj6-16RKQ8Fk1gzEfJC6Qg5aqmVJKjaw).
Earlier cells and failed runs are retained. R2's scoped source milestone is
accepted on the build/oracle evidence below. It remains outside the core and
has no terminal reproduction or independent-audit claim.

## Gate 6: builds pass; original wrapper returns FAIL

The current fresh clone at the registration commit uses geometry SHA-256
`CD4EEF25817D3A5F2EF6F61FDD19D3E8E5C3ECA3B5FC34202DDD7219933E4D79`,
measure SHA-256
`1A345A144A95D2A61076A86EDD23ABF3B097E51F5ADC0E0EDB8EA9AA224B6884`,
and global oracle SHA-256
`2D7122DB41BDE8055F9A3290C98AE22E2DB361B65B12F4BB5C4953AE5D2E09E3`.
The runner verified these exact UTF-8/LF bytes before their respective stages.

The focal build completed successfully at **8171 jobs**, and all **39**
headline oracles exited **0** with only the permitted standard axioms.
The [focal transcript](gate-6-oracle.txt) matches the archived stdout SHA-256
`442064076d3cb410b76cb0d82b2b343aa5796de7618e94252da0f1adf406f99f`.
The unchanged core passed at **8466 jobs**; the complete oracle import set
passed at **8471 jobs**. Consistency and the base dashboard validation passed.
The global Lean process exited **0** after **1450.005648 seconds**.

The original wrapper nevertheless returned **FAIL**, because its parser
`'([^']+)'` cannot read apostrophes inside Lean declaration names. It counted
2850 reports instead of 2854, first missing `YangMills.OS.pow_succ_apply'`.
The [original manifest](gate-6-manifest.json) preserves that FAIL and every
stage field; its whitespace differs from the archived original. This failed
gate is not relabelled or amended.

- Execution: `2026-09-06T11:14:30.527161Z` to
  `2026-09-06T11:54:33.444475Z` (2402.917314 seconds).
- CPU/high-RAM, observed at 50.99 GB. Automatic runtime release followed
  archive preservation; the disconnected UI was observed before 12:56 UTC after
  recovery of the task. Exact allocation and billed connection time are unavailable.
- Full global stdout SHA-256:
  `4ef9016c2f81cda5401363f74459e78a9c9365aca1b817e49e1df3491e493839`.
- Complete archive SHA-256:
  `77c85e48ddf0402548fe7c9c4bb38ebbabbbe76636ecfaa7c4f2f8e32151d14d`.
  The lossless Base64 archive remains in notebook cell 8. Notebook access may
  require the owner's permission; public manifests are not full public logs.

## Separate validation of the saved logs

A short Colab diagnosis at `12:57:58.754252Z`–`12:57:58.780112Z` confirmed
the archive hash and the primed-name parser defect. It emitted no PASS and
automatically released its runtime. The original failure remains immutable.

The separately prepared [saved-log validator](check_gate6_logs.py), UTF-8/LF
SHA-256 `852769894cf1b0ad1489ab83d549e1f8d6854cf6e38087a234258f98e1498c35`,
then checked the same archive on a fresh task-owned CPU/high-RAM runtime.
It checked all stage exits/log hashes, exact source/driver hashes, and every
report's name, order and permitted axiom dependencies. It handles the four
primed names without renaming or dropping any declaration.

Normal and `python -O` modes both exited **0** and produced identical
[JSON stdout](saved-log-validation.json), SHA-256
`3dac65b9d31b74baef8498217deef57f5cfbefbf927c2faf87e9b69b8991f069`.
Each mode rejected all **13** actual data mutations: missing/duplicate/
renamed/reordered/malformed reports, a removed prime, a nonstandard axiom,
changed driver name, nonzero/empty exit, changed log digest, source bytes
and log bytes. The explicit counter is checked without Python assertions.

Result: **39 focal and 2854 global readouts**, including **26 axiom-free**
global readouts, all others using only standard permitted axioms. This
validates the saved successful Lean executions; it does not rerun Lean,
turn gate 6 into PASS or constitute a second fresh source reproduction.

Validation ran `13:03:03.561008Z`–`13:03:04.180011Z` (0.619003 seconds),
then automatically released its runtime. Disconnection was observed before
13:08 UTC. These execution timestamps do not establish billed connection time.
Full output and the prepared validator are preserved in notebook cell 10.

R2 establishes the finite physical measure and reflection identity. R3
positivity and strictly positive centered norm, R4/R5 and 4D continuum
reconstruction remain open. Historical Clay label: **~0% (<0.1%)**, a
convention rather than a measured completion fraction.

## Diagnostic 1: failed geometry elaboration

- Fresh clone at `ba48274f217220ae2aa47ddaddd8e377fb2231a8`, with two
  exact uncommitted UTF-8/LF source overlays.
- `PhysicalWilsonCylinder.lean` SHA-256:
  `5C143537D1B8943249025C60AF6043251C6CCE12BD891D0FFCFF2725326E9C38`.
- `PhysicalWilsonCylinderMeasure.lean` SHA-256:
  `07A91C3113EBDE641F1F06C5FAAB0C56CD18960829891D121EF709022122A090`.
- Execution: `2026-09-06T10:31:02.626263Z` to
  `2026-09-06T10:36:45.089760Z` (342.463497 seconds).
- CPU/high-RAM observed at 50.99 GB. The prepared runner automatically
  released the runtime after preserving the archive; the disconnected UI
  was subsequently observed. Exact allocation/billing duration was not captured.
- Toolchain and pinned Mathlib cache succeeded. The focal build exited **1**
  after 189.053537 seconds. Neither focal oracle nor core/global oracle ran.
- Complete focal log SHA-256:
  `5e57a4427fcbb7385d357e0b030e337bbeadc6baa88470fefc2a85e19ea2eb2c`.
- Complete archive SHA-256:
  `07e4265ff0a9e00ab4ef2b35cf44da68527d4cdf49c0483ce14674d03510d773`.
  Its lossless Base64 export and full manifest are in notebook cell 3.
  The [public manifest](diagnostic-1-manifest.json) transcribes every field;
  whitespace differs from the archived original.

The first error was the concrete class-valued `geometry` declaration being
opaque to instance resolution. `toGaugeConfig` could not synthesize
`FiniteLatticeGeometry 2 2 G`; plaquette numeral elaboration and dependent
dictionary proofs then failed. Compiler-generated recovery placeholders in
this failed log are not source proofs and are not accepted.

The proposed repair makes the constructed geometry reducible and locally
available to instance search. The next draft also supplies explicit Gibbs
integrability of continuous observables. These changes require another run;
this diagnosis is not a successful verification.

## Diagnostic 2: remaining concrete index elaboration

The second fresh clone used the same registration commit, with geometry
SHA-256 `0E668210180C6C687F78B6677CFAC30C8B0A119525779DE8C13F536077B443A6`
and measure SHA-256
`C5E411B71DEA45062B4AF1890476C235CFFC897D0453332B8D209C4669CD31E9`.
The [public manifest](diagnostic-2-manifest.json) transcribes every field;
whitespace differs from the archived original.

- Execution: `2026-09-06T10:39:38.419899Z` to
  `2026-09-06T10:44:19.405672Z` (280.985773 seconds).
- CPU/high-RAM, 50.99 GB; automatic release completed and disconnected UI
  observed. Exact allocation/billing duration was not captured.
- Toolchain/cache succeeded; focal build exited **1**, after 163.146636 seconds.
  The only geometry errors were the two unannotated plaquette numerals at
  lines 109 and 113: Lean could not synthesize `OfNat` for the projected
  plaquette type. The measure module and all oracles remained blocked.
- Complete focal log SHA-256:
  `46739e95e631481876300d8d644402c811c334a549d711d7e6a4cca0d782a20c`.
- Complete archive SHA-256:
  `5a7487d14283953476543838f2426ae8649e7848455e3b92a82cf187f5827858`.
  Lossless Base64 and full manifest are retained in notebook cell 4.

The next draft annotates both indices as `Fin 2`. It also states the exact
dictionary from the density exponent to the mother's Wilson action. This
is another unverified repair, not evidence that the measure proof passes.

## Diagnostic 3: geometry compiles, measure fails

The third fresh clone at the same registration commit used geometry
SHA-256 `CD4EEF25817D3A5F2EF6F61FDD19D3E8E5C3ECA3B5FC34202DDD7219933E4D79`
and measure SHA-256
`599323C5CE1315866061B606F3C10DFE476C97F7070A7A588FA441BC714F5B57`.
The [public manifest](diagnostic-3-manifest.json) preserves every recorded
field; JSON whitespace differs from the archive.

- Execution: `2026-09-06T10:52:05.907252Z` to
  `2026-09-06T10:57:00.562987Z` (294.655735 seconds).
- CPU/high-RAM, 50.99 GB. The runner released the runtime automatically;
  the disconnected UI was observed. Exact billing duration was not captured.
- The concrete geometry module **compiled**, at job 8170 of 8171.
  The measure module failed, so the overall focal exit is **1**
  (157.014127 seconds). Core and all oracles were not reached.
- Errors concern the swap theorem namespace, right-Haar map rewriting,
  scalar-one simplification, second countability for product Borel spaces,
  real-to-complex scalar rewrites, and the Fubini rewrite across measure aliases.
  They are recorded failures, not missing hypotheses supplied by the caller.
- Complete focal log SHA-256:
  `a0d4790ccc1a2baad8621472bb48ea26c327f98f0c6ae19a8e107f03a3c8241d`.
- Complete archive SHA-256:
  `9717363d9be300d0e567efba83eca4fc82d94b3997f52923bbd792479c7cacf4`.
  Full source, logs and lossless Base64 export remain in notebook cell 5.

The revised measure draft reuses the satellite's explicit Haar-map and
scalar-one proofs, supplies second countability from matrix coordinates,
and rewrites complex scalar multiplication explicitly. Another fresh gate
is required. Geometry compilation alone does not accept R2.

## Diagnostic 4: one normalization rewrite remains

Fresh clone at the same registration commit; geometry bytes unchanged from
diagnostic 3. Measure SHA-256:
`BDAFEC9AEF0FA40CD2CF79B16FA3EF0251DE908A82EDB01445A5FE7B3DDBFF51`.
The [public manifest](diagnostic-4-manifest.json) preserves its recorded fields.

- Execution: `2026-09-06T11:01:13.544158Z` to
  `2026-09-06T11:07:21.046792Z` (367.502634 seconds).
- CPU/high-RAM, 50.99 GB; automatic release and disconnected UI observed.
  Exact allocation/billing duration was not captured.
- Geometry compiled. Focal exit **1** (215.249517 seconds), with one error:
  the uninstantiated reverse `integral_const_mul` rewrite in
  `integral_gibbs_eq`, line 200. Earlier topology, Haar and Fubini errors
  were absent. No oracle/core acceptance follows from this failed module.
- Focal log SHA-256:
  `082bf14f5a724ad566c5f6ef2a800dc0d073bc2395e85809be342f4e0e9ede85`.
- Complete archive SHA-256:
  `fffbe23e744bfbf5b50691e76bd4f92da9bca3fc6c7a480e65d48835826d9225`.
  Full logs, source and lossless Base64 export are retained in notebook cell 6.

The next draft uses an explicit intermediate integral and an instantiated
constant-multiplication theorem. It also removes compiler-reported unused
simp arguments. The mathematical statement and 39-headline target are unchanged.

## Diagnostic 5: cast/inverse identity exposed

Fresh clone at the same registration commit; geometry unchanged. Measure
SHA-256 `8DD90B81481BB7183792204A2588B164095BF47A2D424DBB5967587015F25256`.
The [public manifest](diagnostic-5-manifest.json) preserves every recorded field.

- Execution: `2026-09-06T11:09:18.775110Z` to
  `2026-09-06T11:12:47.206869Z` (208.431759 seconds).
- CPU/high-RAM, 50.99 GB; automatic release and disconnected UI observed.
  Exact allocation/billing duration was not captured.
- Focal exit **1** (114.826641 seconds). The explicit calculation now exposes
  the difference between the complex cast of a real inverse and inversion
  after casting. Both remaining goals are in `integral_gibbs_eq`; the
  standard `Complex.ofReal_inv` identity is the next repair.
- Focal log SHA-256:
  `54249c2f3f93a499302f212b16c1ad65ccd1164c4eb49eb35e9a6fd8f25a2d4c`.
- Complete archive SHA-256:
  `3ae8d20fadd84429df046b852da487e2de0b0898e3b7698f747bb728e1f6b968`.
  Full logs/source and lossless Base64 are retained in notebook cell 7.

No oracle or core build ran in this failed unit. The next draft adds the
cast/inverse rewrite; the statement and headline list are unchanged.
