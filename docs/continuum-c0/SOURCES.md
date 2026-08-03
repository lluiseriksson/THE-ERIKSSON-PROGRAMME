# CONTINUUM-C0 sources and attribution boundary

This note distinguishes standard background from what is actually formalized
in this campaign.  Citations are primary papers or monographs; they are not
claims that the cited continuum constructions have been reproduced here.

## Classical background

1. Yu. V. Prokhorov, “Convergence of Random Processes and Limit Theorems in
   Probability Theory,” *Theory of Probability and Its Applications* **1**
   (1956), 157–214.
   DOI: [10.1137/1101016](https://doi.org/10.1137/1101016).

   Classical role: tightness/relative compactness is a measure-level route to
   weak subsequential limits.  CONTINUUM-C0 only defines a precise uniform
   tightness obligation for candidate laws; it proves no Prokhorov theorem and
   constructs no continuum law.

2. K. Osterwalder and R. Schrader, “Axioms for Euclidean Green’s Functions,”
   *Communications in Mathematical Physics* **31** (1973), 83–112.
   DOI: [10.1007/BF01645738](https://doi.org/10.1007/BF01645738).

3. K. Osterwalder and R. Schrader, “Axioms for Euclidean Green’s Functions
   II,” *Communications in Mathematical Physics* **42** (1975), 281–305.
   DOI: [10.1007/BF01608978](https://doi.org/10.1007/BF01608978).

   Classical role: Euclidean axioms, including reflection positivity, are part
   of a reconstruction route to relativistic field theory.  CONTINUUM-C0
   proves only that a real reflection-positive quadratic inequality is closed
   under pointwise scalar limits, conditional on a finite-scale producer.  It
   does not formalize the OS axioms or reconstruction.

4. K. Osterwalder and E. Seiler, “Gauge Field Theories on a Lattice,”
   *Annals of Physics* **110** (1978), 440–471.
   DOI:
   [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916%2878%2990039-8).

   Classical role: lattice approximations of Euclidean gauge fields and
   physical positivity.  The repository’s existing OS modules formalize
   finite `Z₂` instances and interfaces, but no theorem in CONTINUUM-C0
   transports that paper’s full gauge-theory construction to the `SU(2)`
   thermodynamic state.

5. Erhard Seiler, *Gauge Theories as a Problem of Constructive Quantum Field
   Theory and Statistical Mechanics*, Lecture Notes in Physics 159, Springer,
   1982. DOI:
   [10.1007/3-540-11559-5](https://doi.org/10.1007/3-540-11559-5).

   Classical role: a monographic treatment separating lattice gauge theories
   from continuum constructive-QFT obligations.  This separation motivates
   the explicit `CandidateLawRealization`, tightness, compatibility, and
   nontriviality frontiers.

6. James Glimm and Arthur Jaffe, *Quantum Physics: A Functional Integral Point
   of View*, 2nd ed., Springer, 1987.
   DOI:
   [10.1007/978-1-4612-4728-9](https://doi.org/10.1007/978-1-4612-4728-9).

   Classical role: functional-integral and constructive-QFT context,
   including removal of cutoffs and axiomatic regularity.  None of its
   continuum existence results is imported or claimed.

## Formalized here

- The scale topology is Mathlib’s `Tendsto ... atTop (𝓝 0)` on real spacings.
- A canonical one-point cylinder is embedded at the integer coordinate
  `⌊x/aₙ⌋`; translation invariance discharges its constant-coupling
  convergence without postulating a limit functional.
- “Weak limit on tests” is pointwise convergence of actual constructed Gibbs
  state evaluations in `ℝ`.
- Stability of elementary algebraic/order/translation/RP inequalities uses
  uniqueness and order-closedness of real limits.
- The existing KP radius inequality implies the new quantitative bound
  `|β| < 1 / (((16d+1)^2)B)` for `B>0`, hence `|β| < 1/8450` in the concrete
  `d=4`, `B=2` interface and incompatibility with `βₙ → +∞`.
- Tightness and positive limiting variance are named propositions only.

## Not source-upgraded

These citations do not establish any missing repository hypothesis.  In
particular they do not prove `GeometricScalingCompatibility`,
`CandidateLawRealization`, `UniformlyTight`, `HasFluctuatingLimit`, the SU(2)
reflection adapter, eventual separation of multipoint floor anchors,
continuum existence, OS reconstruction, or a mass gap.
