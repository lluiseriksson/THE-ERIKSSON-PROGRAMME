# (16) PR #43 repair: current status

This is a manufacturer status record, not an external audit verdict.  A
concrete inhabitant now exists for every `BetaDomain`; terminal reproduction
and a fresh blind external audit are still required before closure.

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

These are intermediate manufacturer checks, not the terminal two-clone,
complete-oracle, `YangMillsCore`, CI, or blind-audit evidence.

GitHub reports no required checks configured for the PR branch; this is not a
remote-CI pass and remains open evidence debt.

## ABIERTO

- Strengthen the label-two character-ring bridge to a constructed spin-one
  representation if the independent audit requires an actual complement
  rather than the explicit tensor-square identity.
- Seal the documentation-aligned source SHA; run every target and
  `YangMillsCore`, the complete axiom oracle, mutation instruments, CI, and
  binary/LF hashing in two independent fresh Colab clones of that same SHA.
  Require matching hashes, regenerate the non-recursive final transcript,
  and request a new blind external audit.
- Physical-cell identification, reflection/OS positivity, programme Gate 7,
  a paper claim, merge, and manufacturer self-certification remain out of
  scope.
