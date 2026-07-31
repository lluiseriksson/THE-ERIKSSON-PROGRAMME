# (16) PR #43 repair: current status

This is a manufacturer status record, not an external audit verdict.  The
repair is a **PARTIAL MILESTONE** and the gate is not closed.

## EXACTO

- `haarSU2` is the repository's normalized `sunHaarProb 2` measure.
- `CellConfiguration` carries the measurable space transported from its eight
  named SU(2) coordinates; `cellHaar` is the mapped `Measure.pi` product,
  with probability, mass-one, finiteness, and coordinate-marginal theorems.
- `traceRealityConcrete` and `characterBoundConcrete` discharge the trace
  inputs without importing draft PR #39.
- `haarSchurConcrete` reduces the trace convolution entrywise to
  `sunHaarProb_fundamental_entry_orthogonality` using the same concrete Haar
  measure.
- `fubiniCoordinatesConcrete` derives ordinary product Fubini from
  integrability.  The relative coordinate map is a separate measurable Haar
  equivalence with a separate measure-preserving proof.
- `normMomentsConcrete` derives the four witness moments; consequently the
  established witness norm `3/4`, all three orthogonalities, the singlet
  `1/2`, and the factor `1/16` are preserved.
- `weightMeasurabilityConcrete beta` is proved for every real `beta` from the
  eight projections; weight integrability is concrete against `cellHaar`.
- `su2WeylPolynomial` fixes the only low-spin probes consumed by the gate.
  Label one is literally the character of `fundamentalRep`; label two obeys
  the proved tensor-square character-ring identity
  `chi_1 + 1 = chi_fund^2`.
- The conditional front door has no arbitrary measure or function-family
  argument: it fixes `cellHaar` and `su2WeylPolynomial`.

## CERTIFICADO

`manufactured_six_point_theta_gate beta` is conditional on exactly one named
technical record:

- `ManufacturingTechnicalInputs beta.coefficientSeries`, the two nonnegative
  coefficient remainders for the concrete Haar integrals and concrete Weyl
  probes.

The field is not a headline restatement.  It remains a mathematical input,
so neither the beta-one nor uniform front door is a closed certificate.

## VERIFICADO

- Colab isolated cache provenance: Mathlib
  `07642720480157414db592fa85b626dafb71355b`; public clone, no token and no
  push from Colab.
- `YangMills.SU2ThetaPrism.Analysis` at `70bb53bc...`: 8182 jobs, 2 requested
  jobs on 2 host CPUs, 59 seconds, exit 0.
- `YangMills.SU2ThetaPrism.Endpoint` at `242567fa...`: 8185 jobs, 2 requested
  jobs on 2 host CPUs, 60 seconds, exit 0.
- Expanded `YangMills.SU2ThetaPrism.Oracle` at `156bea65...`: 8186 jobs,
  2 requested jobs on 2 host CPUs, 65 seconds, exit 0; all 33 printed
  declarations report exactly `[propext, Classical.choice, Quot.sound]`.
- The rational certifier succeeds under normal Python and `python -O`.
- Ten mutations are rejected under both modes, including `1/2 -> 1/3` and
  enlargement to all beta.  The syntactic headline guard passes and rejects
  its registered cheat fixtures.

These are intermediate manufacturer checks, not the terminal fresh-checkout,
complete-oracle, `YangMillsCore`, CI, or blind-audit evidence.

GitHub reports no required checks configured for the PR branch; this is not a
remote-CI pass and remains open evidence debt.

## ABIERTO

- Prove `CoefficientRemainderSteps` for `su2WeylPolynomial`, at minimum for
  `beta = 1`; no inhabitant of `ManufacturingTechnicalInputs 1` exists yet.
- A pin-exact search found no SU(2) Weyl integration formula.  The available
  `HaarToSphere` construction is not an SU(2)-Haar identification.  The
  repository has the trace second moment but not `integral (chi ^ 4) = 2`;
  closing the proposed spin-one bound therefore requires that normalized
  one-variable integration brick or a concrete irreducible spin-one
  decomposition.  The direct spin-half Haar-symmetry bound is preregistered
  separately and does not close this field by itself.
- Strengthen the label-two character-ring bridge to a constructed spin-one
  representation if the independent audit requires an actual complement
  rather than the explicit tensor-square identity.
- Only after the coefficient obligation closes: run every target and
  `YangMillsCore`, the complete axiom oracle, CI, binary/LF hashing, and a
  fresh checkout of the published refs; regenerate the non-recursive final
  transcript and request a new blind external audit.
- Physical-cell identification, reflection/OS positivity, programme Gate 7,
  a paper claim, merge, and manufacturer self-certification remain out of
  scope.
