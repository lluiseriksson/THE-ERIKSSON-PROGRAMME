# Physical Wilson cylinder R2 evidence

All proof execution uses the task-owned CPU/high-RAM Colab notebook:
[R1/R2 source and complete evidence archives](https://colab.research.google.com/drive/1Hj6-16RKQ8Fk1gzEfJC6Qg5aqmVJKjaw).
Earlier cells and failed runs are retained. R2 has no accepted source gate yet.

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
