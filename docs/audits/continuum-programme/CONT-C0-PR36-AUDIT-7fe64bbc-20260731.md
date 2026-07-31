# Independent CONT-C0 audit — PR 36 at `7fe64bbc`

Snapshot:

```text
producer: 7fe64bbced729337f6a1060d731e661384863c42
tree:     d8742bf31f3db02c80f1060074a012b1228b12ed
PR base:  1e6113a10c407ba2964af2713aef26c62bbd1157
main:     1f81ec43404ae2a8c72a8c934807d4b03b8680c9
observed: 2026-07-31T07:17:04.7583792Z
PR:       https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/36
```

Final freshness seal at `2026-07-31T07:32:50.7440095Z`: the producer head
remained `7fe64bbc`; public `main` had independently advanced to `f8592f62`.

An initial clean checkout at `72cae3d2` was discarded when the mandatory
freshness check found that the public producer had advanced. A second check
found the documentation-only move `cb8fec00 -> 7fe64bbc`; that complete delta
was reviewed and the changed Lean source was re-elaborated. This report audits
the superseding head.

## Executive verdict

**PASS, scoped** as an honest scale-indexed transport substrate:

- `ScaleSequence` carries a positive `a_n -> 0`;
- every discrete state is definitionally the repository's constructed
  thermodynamic infinite-volume Gibbs state, not an arbitrary state field;
- `weakLimitValue` is selected only after convergence of actual discrete
  expectations and is pointwise unique;
- normalization, real linearity, positivity, translations, conditional real
  reflection positivity, and factorization are correctly transported under
  their explicit premises;
- a fully typed `d=4`, SU(2), positive strong-coupling family shares one index
  among `beta(k)`, the plaquette offset `2k`, and
  `a_k=1/(k+1)`;
- its declared physical separation tends to `2`, while its actual connected
  infinite-volume correlation tends to zero uniformly for
  `|beta(k)| <= 10^-6`;
- the code proves that the present KP state producer cannot accommodate a
  coupling schedule tending to `+infinity`.

**BLOCKED** as a continuum Yang--Mills candidate. There is no common candidate
law, tightness proof, physical/RG scale bridge, counterterm or renormalised
trajectory, positive limiting variance, OS reconstruction, or continuum mass
gap. At the only discharged nonconstant scale-indexed two-point sector, the
connected correlation vanishes at declared physical separation `2`; this is
compatible with an ultralocal or otherwise trivial limit and therefore cannot
serve as nontriviality evidence.

The producer states these limitations. There is no FAIL witness against its
bounded transport contract, and no merge is performed.

## Registered-gate audit

### Regulator family — BLOCKED

`ScaleSequence` and `GibbsStateSequence` make the lattice spacing, probability
Haar measure, plaquette energy, energy bound, coupling sequence, and KP regime
literal. However, `S.state n` has already taken the thermodynamic limit through
`integerInfiniteLocalGibbsState`; C0 has no remaining finite-volume parameter,
physical-volume trajectory, or boundary-condition family. There are no
renormalised parameters.

For the canonical pair, the order actually proved is precise:

```text
fixed k
  -> construct the infinite-volume state/correlation
  -> then send k -> infinity with a_k = 1/(k+1), offset = 2k.
```

That nested order receives PASS at its declared scope. It is not a joint
continuum regulator construction.

### Arbitrary-limit and circularity tests — PASS, scoped

`GibbsStateSequence` stores no state functional. Its state is constructed from
finite-lattice Gibbs data and a proved KP regime. `HasWeakLimit` says that each
actual real expectation sequence has some limit. `weakLimitValue` uses
`Classical.choose`, but `tendsto_weakLimitValue` uses the corresponding
`choose_spec`, and Hausdorff uniqueness gives `weakLimit_unique`.

The general transport theorems assume `HasWeakLimit`; they do not prove it and
are not credited as doing so. The two compiled examples discharge it only
because the coupling/state is constant and the one-point moving observable is
removed by exact integer-translation invariance. Thus there is no arbitrary
comparison functional hidden in the data and no hypothesis is repackaged as a
general continuum-existence conclusion.

### Topology, laws, and tightness — BLOCKED

The only constructed limit topology is pointwise convergence in `R`.
`CandidateLawRealization` names laws on one fixed topological measurable space,
test functions, integrability, and expectation matching, but no instance is
constructed. `UniformlyTight` is only a definition. The topology and sigma
algebra are not required to be Borel-compatible in the abstract structure.

Accordingly, scalar first-moment convergence is not promoted to tightness,
precompactness, a field/distribution law, or measure uniqueness.

### Full sequence and uniqueness — PASS at pointwise level

All credited limits use `Tendsto ... atTop` for the complete natural-number
sequence. No subsequence result is advertised as a full limit.
`weakLimit_unique` proves pointwise uniqueness for any two comparison
functionals reached by the same expectation sequence. This does not establish
uniqueness of a still-absent candidate probability law, and the report credits
no such result.

### Scale and renormalisation — BLOCKED

`tendsto_axisPairPhysicalSeparation_reciprocal` proves the numerical identity

```text
(1/(k+1)) * (2k) -> 2.
```

The newer `d4ScaleIndexedTwoPointData` correctly places that coordinate and the
actual state correlation in a single pair at the same index. This closes the
earlier interface mismatch between “moving observable” and “scale-indexed
state”.

It still does not instantiate `ScaleConventionCompatible` with the
repository's RG spacing, nor `GeometricScalingCompatibility` for a continuum
test family. No counterterm, wave-function/observable normalization, running
renormalised coupling, or continuum action is given. Instead
`no_asymptotically_free_scaling_in_KP_regime` proves a hard wall for the
available state producer.

### Nontriviality — BLOCKED

The positive coupling and four-edge support prove that the discrete example is
not the empty or `beta=0` toy model. They do not prove a nontrivial limit.
`HasFluctuatingLimit`, which requires positive limiting variance of a genuine
test, remains uninhabited.

The strongest new endpoint proves:

```text
(physical separation, connected correlation) -> (2, 0).
```

That is a valid uniform clustering statement, but it does not exclude a
deterministic, Gaussian/free, constant, or ultralocal continuum theory. In
particular, decay to zero at a fixed nonzero declared physical separation is
evidence that must be reconciled with nontriviality, not evidence for it.

## Audit of the two-commit freshness delta

`76bf5e0f` adds the scale-indexed coupling family and
`tendsto_d4ScaleIndexedTwoPointData`. The proof consumes the real
`sunHaarProb 2` state and `su2D4UniformLocalKPRegimeOfBound (beta k)` at each
index. The uniform estimates use only the declared
`|beta(k)| <= explicitStrongCouplingRadiusD4`.

`cb8fec00` updates documentation to expose the corresponding scale, law,
tightness, renormalisation, and fluctuation frontiers. No changed declaration
constructs one of those missing producers.

`7fe64bbc` changes only the docstring of `d4ScaleIndexedTwoPointData` and four
charter lines. It correctly narrows the pair to a bookkeeping product of two
independent limits and records the coarse bound's moderate-distance
limitations. No theorem body or type changes.

The new uniform constant `C = 32000000000000` is deliberately coarse and
independent of `k` and `beta(k)` within the strong-coupling window. Its size is
irrelevant to the limit because it multiplies `exp(-k/100)`. It has no claim to
physical units or cutoff-uniform renormalised meaning.

## Clean-checkout evidence

A new public clone was checked out detached at
`7fe64bbced729337f6a1060d731e661384863c42`; tracked status and
`git diff --check` were clean. Pin hashes:

| Input | SHA-256 |
|---|---|
| `lean-toolchain` | `8C46C0308E92095E478BCFAE7C357327E88C5A624B54ABF5AD1660EE0E51DF5A` |
| `lake-manifest.json` | `E2F2D45A5FEF5AE352E6F8BE858726D603D83FDE30D740A14A8A2A588579381D` |
| `lakefile.lean` | `09D3FF29B030A20C396CDD5F729230EEB7BCDE3AE91CDA519C0643AC6B715BD5` |

Changed load-bearing hashes at the final head:

| File | Git blob | SHA-256 |
|---|---|---|
| `CorrelationGeometry.lean` | `faab604714bc0ee0c0fd33dca07b93696e903056` | `0AF9EE0F91485109A2D9C5D1D55BBE068BF2AC66B6204500827D1C2FEBFA3E55` |
| `TwoPointFactorization.lean` | `2af5ae87860649d4a25415018d8dd6fd1977903f` | `8D00218092AF8B3AA70AA0FD84374D8D9E15AA551AE8302C89CF9F6E284FF9CB` |
| `Oracle.lean` | `431ed6d210ea24388a59b0b6ea9e2a65f2727295` | `EA0C344CBE825712E47708F8E09DE7F2D81A89040DD6F5E6C62540C51D7CC026` |

An exact-head, clean producer worktree supplied only build cache after its
HEAD, status, three pins, and source blobs matched the audit checkout.
`TwoPointFactorization.lean` was nevertheless re-elaborated directly from the
clean source:

```text
lake env lean YangMills/Continuum/TwoPointFactorization.lean
exit 0
elapsed 122407 ms
```

After the final documentation-only move, the exact `7fe64bbc` source was
re-elaborated again with `exit 0` in `83076 ms`.

The only diagnostics were four style lints about `<;>`. An earlier target
build at `72cae3d2` was discarded when the head moved. At the final head,
parallel target/oracle attempts were terminated by local memory pressure while
other repository jobs were active; they emitted no Lean error. The direct
load-bearing source elaboration is dispositive for the new mathematical delta.

After the competing jobs cleared, both oracle commands were repeated
sequentially:

```text
lake env lean YangMills/Continuum/Oracle.lean
exit 0
elapsed 67619 ms

lake env lean oracles/CONT-C0-PR36-7fe64bbc-oracle.lean
exit 0
elapsed 72576 ms
```

All 28 producer headlines and all 10 independently selected headlines emitted
exactly `[propext, Classical.choice, Quot.sound]`.

Static checks returned zero `sorry`, zero verified-core axioms, and a valid
nine-file source catalog. `check_module_prose.py` reports one mechanical
failure because `WeakLimit.lean` backticks the explicitly absent identifier
`ContinuumState`; the sentence says there is deliberately no such structure.
This is a checker false positive, not a semantic headline mismatch.

The producer's `EXTERNAL-AUDIT.md` and model telemetry were not used as
evidence. This desk independently read the source and executed the checks.

## Independent-model disclosure

The one permitted Fable High request returned HTTP 429 with `is_error=true`
and no verified Fable-5 output; it was rejected and not retried. Exact
`claude-opus-5` attempts produced no acceptable JSON. Neither model supplied
evidence or a conclusion for this report.

## Final status

Manifest: `runs/CONT-C0-PR36-7fe64bbc.json`.

```text
PASS:    7
FAIL:    0
BLOCKED: 6
```

The branch now has a genuine scale-indexed strong-coupling two-point theorem.
The candidate-law, tightness, renormalisation, and nontriviality gates remain
open exactly where the producer says they do.
