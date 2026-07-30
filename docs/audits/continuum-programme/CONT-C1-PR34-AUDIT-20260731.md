# Independent CONT-C1 audit — PR 34

Audit time: `2026-07-31` (Europe/Stockholm)  
Producer PR: <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/34>  
Base: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`  
Audited head: `0a46e266fc4808332ed20d2ab4611bfc271b208b`  
Audited tree: `53c767ee27cd524f3316b9cab9dd1efa18e75427`

## Executive verdict

- **PASS**: the finite-cap theorem is correct for the locally defined KP
  predicate on the nonnegative branch. The head imports the real producer,
  proves proposition equality at `t=epsilon=1`, consumes
  `sun_clustering_window_nonempty`, and partially applies the actual
  `sun_two_plaquette_correlator_bound`.
- **PASS**: the cap is independent of lattice extent, physical volume, and
  cutoff. The abstract `beta -> +infinity` no-go is non-circular and its
  positive-coupling premise is non-vacuous.
- **FAIL with witness**: the advertised positive physical convention
  `beta2D=1/(g2*a^2)` is not the coupling convention of the checked Gibbs
  consumer. The consumer uses `exp(-beta * sum ReTr(U_p))`; the usual
  positive Wilson weight is proportional to `exp(+beta_phys * sum ReTr(U_p))`.
  Thus the physical positive inverse coupling maps to a negative repository
  parameter (and may carry a trace-normalisation factor), whereas the formal
  eventual theorem assumes `beta -> +infinity`. The KP cap itself is
  sign-symmetric because it contains `abs beta`, but the required
  absolute-value or `atBot` corollary and the action-normalisation bridge are
  absent.
- **BLOCKED**: E2 remains open exactly as the producer says. No Wilson
  `U(1)` factorisation, Bessel integral/series bridge, explicit `O(a^2)` rate,
  continuum measure, nontriviality theorem, OS reconstruction, or physical
  mass gap is credited.

The PR is therefore a valid negative lemma with a real typed KP bridge, but
not yet a physically normalised cutoff trajectory. No merge is recommended by
this desk.

## Supersession record

The first audit checkout fixed
`b06fb6b8f44f7002fffaa2b371f39c790f42b447`. During execution the public PR
advanced through `4c0f8032b78f58702a1c7ea73894e40053d124db` and
`6957a633ab4870d56bf3bb01de724c1da6adf2dd`, then advanced again after the
first clean build to `0a46e266fc4808332ed20d2ab4611bfc271b208b`.
All earlier checkouts are historical only. The dispositive static, canary,
direct-Lean, target-build, and sign-witness checks were repeated at
`0a46e266`.

At the audited head the draft PR was open, with 16 changed files, 1,313
additions, no deletions, and a successful “CI – Epistemic
Honesty Enforcement” check.

## Clean-checkout and provenance

A public clone was checked out detached at the audited head. Its tracked
status was clean. The dependency cache was accepted only after all three
project pin inputs matched the cache owner:

| Input | SHA-256 |
|---|---|
| `lean-toolchain` | `8C46C0308E92095E478BCFAE7C357327E88C5A624B54ABF5AD1660EE0E51DF5A` |
| `lake-manifest.json` | `E2F2D45A5FEF5AE352E6F8BE858726D603D83FDE30D740A14A8A2A588579381D` |
| `lakefile.lean` | `09D3FF29B030A20C396CDD5F729230EEB7BCDE3AE91CDA519C0643AC6B715BD5` |

Only `.lake/packages` was junctioned to the verified cache. The producer
checkout retained its own `.lake/build`.

Canonical Git-blob hashes (LF bytes):

| File | Git blob | SHA-256 |
|---|---|---|
| `YangMills/Continuum/TightnessScaleNoGo.lean` | `8c2eb4e0fa638179f3fc8b516f13e27fcc303499` | `044B013DB15CE2408A4DFB226642FAF1EB56EB5C3DD61D2D49053726652B10DA` |
| `YangMills/L1_GibbsMeasure/TwoPlaquetteCorrelator.lean` | `394c61a2340215114cd844e4eaea010581810dca` | `B015B8C2F7DC8DC8F242C7295D56BFBD70AC2252F410E238F6AE2286FA0B19EF` |
| `scripts/continuum_c1_beta_cap_audit.py` | `bb9c79e5d1282cb006c0913837bafd57cd27375c` | `13CFDFAF610445630C47E431B0518955A846D129BFA2B26B57B2E678C1D2BFD3` |
| `scripts/continuum_c1_tail_audit.py` | `643cab07b867afdf67210bcc1b51a2bb0f94ac3c` | `D044D87C8E29B0ABF67FCF3A562BE22EEE344F055A9B69ED6D141BC33EA06438` |
| `scripts/continuum_c1_window_canary.py` | `513d2440568bbcf19ee4ab32864a71b781ed4464` | `E81C8B93A4BA62994E8E78770AAB1AD0B7EB181C15A10A6CF1D52C4EA8BEDC09` |
| `docs/continuum-c1/BUILD-TRANSCRIPT.md` | `4785321bc1dd3c49bf88a65044d487080e8dc8c5` | `C66A9F82092D1E5929CD8342D2EA9FE21D542D15E15F9F1DCB96433B848EDAD0` |

The two script hashes printed by the producer are the canonical LF hashes and
match the committed blobs. Windows working-tree CRLF hashes differ, as
expected; they are not evidence of a content mismatch.

## Claim-level audit

### E1-A — identity with the checked KP radius: PASS

`TightnessScaleNoGo.lean:6` imports the actual correlator module.
`kpRadiusAtUnit_iff_checkedWindow` at lines 65-71 proves by `rfl` that the local
predicate is the checked radius conjunct at `t=epsilon=1`.
`kpRadiusAtUnit_nonempty_from_checkedWindow` at lines 76-85 consumes
`sun_clustering_window_nonempty`, and
`checkedCorrelatorAfterKPRadiusAtUnit` at lines 90-101 partially applies the
actual correlator theorem through its `hr` argument.

This closes the drift defect present at superseded head `b06fb6b8`.

### E1-B — finite cap and non-vacuity: PASS

For `Nc>0`, `beta>=0`, and `s>0`, lines 153-190 prove

```text
KPRadiusAtUnit d Nc beta s
  -> beta < log(1 + 1 / ((16d+1)^2 exp(3))) / Nc.
```

The proof drops a strictly positive `s` contribution, so the cap is necessary,
not sufficient. It contains `d` and `Nc` only. Lines 76-85 provide a
positive-beta witness from the checked producer; lines 104-124 independently
prove a numerical radius witness.

The deterministic script reproduced:

```text
d=4, Nc=3: 3.927950692443e-06
d=4, Nc=2: 5.891926038665e-06
d=3, Nc=2: 1.036787842219e-05
```

The binary64 output is diagnostic only; the Lean declaration is the proof.

### E1-C — abstract eventual statement: PASS, scoped

Lines 215-226 prove eventual failure for a trajectory tending to `atTop`, with
fixed positive `s`. This is sufficient for the producer's explicitly stated
nonnegative convention. It is not a theorem about construction of a
continuum measure, and the PR does not claim one.

### U1 — physical Wilson sign and normalisation: FAIL with witness

The checked consumer hard-codes:

```text
fundamentalObservable Nc U = ReTr(U)
wilsonAction pe A = sum_p pe(H_p(A))
Gibbs weight = exp(-beta * wilsonAction pe A).
```

These are at `SchurPhysicalBridge.lean:48-52`,
`WilsonAction.lean:39-42`, and `GibbsMeasure.lean:83-106`.

By contrast, the C1 E2 text uses the positive Fourier weight
`exp(beta*cos(theta))` and defines `beta2D=1/(g2*a^2)>0`. With the checked
consumer and `pe=ReTr`, positive repository `beta` produces
`exp(-beta*ReTr)`, not `exp(+beta*ReTr)`. Matching the usual positive Wilson
weight therefore requires a sign change in the repository parameter (and an
explicit trace/group normalisation).

Finite witness: take one plaquette with declared energy `1` and any
`beta>0` (for the C1 `U(1)` target this is `theta=0`). The positive Wilson
sign gives `exp(beta)` while the generic checked Gibbs convention gives
`exp(-beta)`. They are unequal. This witnesses the missing convention bridge;
it does not assert that the current `SU(Nc)` consumer is already a `U(1)`
model.

The isolated executable witness
`audit_cont_c1_pr34_sign.py` verified the exact producer SHA and source
fragments, then returned:

```text
audit_status: PASS
claim_verdict: FAIL
beta: 1
c1_positive_weight: 2.718281828459045
checked_gibbs_weight: 0.36787944117144233
equal: false
```

The radius bound depends on `abs beta`, so the negative no-go can be repaired
without changing its numerical cap. The audited head does not contain the
needed theorem for `abs(beta(i))->infinity` or `beta(i)->-infinity`, nor a
typed equality relating the physical Wilson action to the checked consumer.
The failure is limited to the advertised physical instantiation; it does not
invalidate E1-A or E1-B.

### E2 and continuum claims: BLOCKED

The producer labels E2 open. Independent search found no theorem in the
changed artefact providing:

- a `U(1)` free-boundary Wilson factorisation;
- an equality between the repository Gamma-series `besselIReal` and the
  Fourier integrals of `exp(beta*cos(theta))`;
- the preregistered `3*g2^2*A*a^2` error;
- a regulator family and tightness/uniqueness result;
- nontriviality, OS reconstruction, or a physical mass gap.

The isolated Haar-tail script concerns exactly `beta=0` and is correctly
labelled diagnostic. Absence of a counterexample is not promoted to evidence
for any positive-beta law.

## Dependency and validity table

| Name | Units | Depends on `a` | extent / physical volume | cutoff | coupling | support / renormalisation scale | Validity and uniformity |
|---|---|---:|---:|---:|---:|---:|---|
| `KPRadiusAtUnit` | dimensionless proposition | no | no / no | no | yes: `beta`; also `s,d,Nc` | no / no | strict radius, `s>0` when consumed |
| `kpBetaCap(d,Nc)` | dimensionless coupling parameter | no | no / no | no | no | no / no | finite positive for `Nc>0`; uniform in extent, volume, and `a` |
| `ScaleDict.beta2D` | dimensionless only if `[g2]=length^-2` | yes, `a^-2` | no / no | yes through `a` | yes: `g2` | no / no | internal 2D convention; physical consumer bridge fails U1 |
| correlator lattice rate at `t=epsilon=1` | inverse lattice steps | no explicit `a` | volume-free value and domain | not cutoff-uniform along divergent `abs beta` | yes through the KP domain | observable bounded by one | cannot be transferred to a positive physical mass |

The cap's lack of volume and cutoff variables is genuine. It proves an
obstruction to reusing this strong-coupling estimate; it is not a positive
cutoff-uniform estimate.

## Independent command transcript

At audited head:

```text
python scripts/continuum_c1_beta_cap_audit.py
exit 0

python scripts/continuum_c1_tail_audit.py \
  --nc 2 --a-num 1 --a-den 10 --radius 1000
exit 0

python scripts/continuum_c1_window_canary.py --self-test
exit 0; textual radius comparison and mutation self-test PASS

python scripts/check_module_prose.py \
  YangMills/Continuum/TightnessScaleNoGo.lean
exit 0; modules checked: 1; failures: 0

python scripts/check_consistency.py
exit 0; zero sorry; zero verified-core axioms

python scripts/source_db.py verify
exit 0; 9 catalog files; no structural errors

python docs/audits/continuum-programme/audit_cont_c1_pr34_sign.py \
  --checkout <clean-producer-checkout> \
  --expected-sha 0a46e266fc4808332ed20d2ab4611bfc271b208b
exit 0; audit_status PASS; claim_verdict FAIL

git diff --check 7c6aaab2...0a46e266
exit 0
```

The final clean target-build transcript and oracle output are recorded in the
closing section below.

## Source audit

The technical source packet uses primary papers, publisher records, an
author-hosted paper, and authoritative lectures. Its transfer limitations are
stated. In particular, Driver's two-dimensional convergence result is not
credited as the missing explicit rate, and the inaccessible full
Osterwalder--Seiler theorem is not used for a numbered technical claim.

Luescher's lecture notes independently support the cutoff and renormalisation
audit: the lattice is a regulator with cutoff proportional to `a^-1`, the
continuum limit requires `a->0`, and renormalised observables can require
scale-dependent factors. Those facts do not supply the missing C1 producer.

## Independent-model disclosure

The one permitted Fable High request had already returned HTTP 429 with
`is_error=true`, empty `modelUsage`, and no verified Fable 5 output. It was
rejected and not retried. Earlier exact-identifier `claude-opus-5` attempts
produced no acceptable JSON before timeout. Neither model contributed to this
dictamen.

## Closing build result

From the clean detached checkout:

```text
lake build YangMills.Continuum.TightnessScaleNoGo
exit 0
Build completed successfully (8198 jobs).
```

At the superseding head, direct Lean returned exit `0` in `188525 ms`; the
target build returned exit `0` in `125267 ms` and built the changed producer.
All seven producer `#print axioms` queries emitted exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Warnings replayed from pre-existing dependency modules; the producer target
itself emitted its seven informational oracle lines and no project axiom.
Because the module is intentionally absent from `YangMillsCore`, the global
job-count integration threshold is not applicable. House build verdict:
**PASS**.
