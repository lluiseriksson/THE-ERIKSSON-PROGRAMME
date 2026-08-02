# (16) PR #43 repair: current status

This is a manufacturer status record, not an external audit verdict.  A
concrete inhabitant now exists for every `BetaDomain`.  Terminal reproduction
in two independent fresh Colab clones is DONE and recorded below; the only
remaining requirement before closure is a fresh blind external audit.

**Build provenance.**  The compiled source `08155607cacca04f3f7a507a78762f88fffd395d`
descends from `43c003b2c0c98aceeabbf10ba28a4783de5859f1`, which is its real
build base.  It does NOT descend from the PR's declared base
`26306b8f30e826b0bcb7c4caf6a5a42473ab5fd8`: that commit is not an ancestor,
the two histories diverge at `43c003b2`, and the source is 55 commits ahead
and 4 behind it.  Any comparison against `26306b8f` compares against a tree
that was never the starting point.

**Core integration: none, and the job count says so.**  `YangMillsCore.lean`
at `08155607` contains zero imports and zero mentions of any `SU2ThetaPrism`
module.  The measured 8464 jobs is therefore the inherited baseline with no
increment; it is not evidence of core integration and must not be read as
such.  This lane sits outside the verified core, exactly like PR #39 and
PR #40.

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
- The concrete front door has no arbitrary measure, function-family, or
  technical-input argument: it fixes `cellHaar`, `su2WeylPolynomial`, and the
  uniform technical-input constructor.

## CERTIFICADO

The internal lemma `manufactured_six_point_theta_gate` remains factored
through one technical record whose only field is the spin-one remainder.  The
public `manufactured_six_point_theta_gate_concrete` supplies the record using:

- the quaternion-coordinate second- and fourth-moment theorems;
- the central-Haar `cosh` symmetrization;
- the signed remainder estimate across both regions `|chi| < 1` and
  `1 <= |chi|`; and
- `spinOneCoefficientRemainderStepConcrete` for every nonnegative beta.

Thus `manufacturingTechnicalInputsConcrete beta hbeta` inhabits
`ManufacturingTechnicalInputs beta` for every `hbeta : BetaDomain beta`.
`manufacturingTechnicalInputsConcrete_betaOne_specialization` is only the
named beta-one specialization of that uniform constructor.

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
- Direct spin-half coefficient target at `a6bf8170...`:
  `YangMills.SU2ThetaPrism.Coefficients`, 8184 jobs, 2 requested jobs on
  2 host CPUs, 52 seconds, exit 0.
- Minimized-input endpoint and expanded oracle at `fcbe7194...`: 8186 jobs,
  2 requested jobs on 2 host CPUs, 96 seconds, exit 0; all 38 printed
  declarations, including the five new coefficient-route declarations and
  `manufactured_six_point_theta_gate`, report exactly
  `[propext, Classical.choice, Quot.sound]`.
- Uniform inhabitant source at
  `3c198717e1b53b016803e3db76fda88f99314f89`: fresh public Colab clone,
  Lean `v4.29.0-rc6`, Mathlib `07642720...`, 8 host CPUs with Lake-default
  parallelism.  `Coefficients`, `Endpoint`, and the independent `#check`
  file passed; the checked type is
  `manufacturingTechnicalInputsConcrete (beta) (hbeta : BetaDomain beta) :
  ManufacturingTechnicalInputs beta`.  The resulting `.olean` hashes were
  `3bb7d37a...e9385c` for `Coefficients` and
  `235ff3fd...1de157` for `Endpoint`.
- The rational certifier succeeds under normal Python and `python -O`.
- Ten mutations are rejected under both modes, including `1/2 -> 1/3` and
  enlargement to all beta.  The syntactic headline guard passes and rejects
  its registered cheat fixtures.

- Terminal source SHA `08155607cacca04f3f7a507a78762f88fffd395d`
  was reproduced in two independent fresh Colab CPU/high-RAM clones.  All nine
  exact targets and `YangMillsCore` built; 48 oracle headlines reported only
  `propext`, `Classical.choice`, and `Quot.sound`; instruments passed under
  normal Python and `-O`.
- The two deterministic manifests are byte-identical with SHA-256
  `8fab9c9cff877133ff26dc50316f65f0e8d7a96aeee5cd8f10c2e186fa27ad52`.
  Source RAW/LF hashes, ten `.olean` hashes, and the measured failures are in
  `SU2-THETA-PRISM-TRANSCRIPT-20260801.txt` and the checked-in manifest.
- GitHub honesty run `30704212187`, job `91380399007`, passed on the compiled
  SHA.  It remains a syntactic check rather than mathematical certification.

These are manufacturer reproduction results, not a blind-audit verdict.

## ABIERTO

- Strengthen the label-two character-ring bridge to a constructed spin-one
  representation if the independent audit requires an actual complement
  rather than the explicit tensor-square identity.
- Request a new blind external audit of the published refs.  Do not treat the
  manufacturer's matching two-clone manifests as that audit.
- Physical-cell identification, reflection/OS positivity, programme Gate 7,
  a paper claim, merge, and manufacturer self-certification remain out of
  scope.
