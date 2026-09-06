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

The first error was the concrete class-valued `geometry` declaration being
opaque to instance resolution. `toGaugeConfig` could not synthesize
`FiniteLatticeGeometry 2 2 G`; plaquette numeral elaboration and dependent
dictionary proofs then failed. Compiler-generated recovery placeholders in
this failed log are not source proofs and are not accepted.

The proposed repair makes the constructed geometry reducible and locally
available to instance search. The next draft also supplies explicit Gibbs
integrability of continuous observables. These changes require another run;
this diagnosis is not a successful verification.
