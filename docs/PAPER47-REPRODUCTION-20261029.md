# Exact-paper reproduction dossier, 29 October 2026

This dossier concerns the existing paper *Exact-Kernel Fourier Families Obstruct
Every Penalty Factored Through a Block Map in a Flat Lattice Gauge Form*,
[ai.viXra 2608.0015v1](https://www.ai.vixra.org/abs/2608.0015) and
[AIRR ARR-2026-7EPM3V3DP796BBRR v1](https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v1/).
Internal manuscript edition 1.4 is distinct from the public archive version v1.
This is a reproducibility supplement to that existing record, not a new paper.

## Frozen objects and executable recipe

The exact public PDF has SHA-256
`48b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7`.
The source packet `output/pdf/critical_rescaling_fourier_no_go_sources_v1.4.zip`
has SHA-256
`ef5501145398b5f672dcdfb66206c1f5f280f2c61b231d2c9ac0e1a4e693f82a`.

For an executable checkout use the **complete tree** at
`7b25bfb39357406cf61880e3ac0428d7d1ba3449`, not current main and not just the
eleven Lean bodies in the packet. The packet names focal files but does not
contain every imported prerequisite. The earlier anchor
`f21539ed0bb880a04078de369bf5cbf063f7b101` covers the earlier chain; it is not
the complete later factorized-repair extension. This distinction was found by
static import inspection, not by inventing an observed compilation failure.

In a fresh Colab Pro+ Linux CPU/high-RAM runtime, with official Elan installed:

```sh
git init paper47
cd paper47
git remote add origin https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
git fetch --depth=1 origin 7b25bfb39357406cf61880e3ac0428d7d1ba3449
git checkout --detach FETCH_HEAD
lean --version
lake exe cache get
lake build YangMills.RG.PhysicalCriticalRescalingFourierFactorizedRepair
lake env lean YangMills/RG/PhysicalCriticalRescalingFourierFactorizedRepairOracle.lean
```

Before execution, check the eleven LF-normalized bodies against the frozen
manifest, `lean-toolchain` against `leanprover/lean4:v4.29.0-rc6`, and Mathlib
against `07642720480157414db592fa85b626dafb71355b`. The accompanying frozen
notebook performs these checks explicitly; no acceptance decision uses Python
`assert`. Prepare disconnected and release the runtime when the unit finishes.

## What the focal oracle checks

All names below have namespace `YangMills.RG`:

| Declaration | Scope |
|---|---|
| `flatBlockConstraintQCLM_blockFourierMode_eq_zero` | Exact annihilation by the flat block map |
| `flatGaugeHodgeK0_inner_blockFourierModeCochain_of_ne` | Flat Hodge energy of the transverse witness |
| `factorizedFlatPoincare_fourier_lower_bound` | Necessary bound from the witness |
| `volumeUniformFactorizedFlatPoincareGate_fourier_false` | Failure of the stated unrestricted flat gate |
| `repairedFlatPoincare_blockFourier_rayleigh_eq` | Exact repaired Rayleigh identity on that witness |
| `repairedFlatPoincare_blockFourier_budget` | Necessary repair budget on that witness |

The oracle must emit exactly these six reports in order, each with exactly
`propext`, `Classical.choice`, and `Quot.sound`. The factorized endpoint is in
dimension four. The manuscript's higher-frequency min-max argument is analytic;
this focal check does not turn it into a machine-checked declaration. The repair
budget is necessary, not sufficient for coercivity on all fields.

## Evidence boundary

Run006 completed successfully in its own fresh clone, but its complete ZIP was
not recovered. Only the preserved UI report supports its six oracle reports and
target `.olean` hash. It cannot replace a complete evidence package.

Run007 produced a recovered ZIP with SHA-256
`bb01c7a51ce8af790ad2a6489cb8f07b1a031a4fb77d010180fae1ffa13b9f08`.
Its twelve manifest entries, eleven source bodies, nine exit-zero steps and six
raw oracle reports were checked. Its target `.olean` SHA-256 is
`6e7a650818feefcd7f044f1db5ce3b5090da725a9c81ab72c391700929f91c5e`,
matching the earlier UI-derived run006 value.

Run008 used another fresh Colab clone at the same source SHA and produced ZIP
SHA-256 `1d836d08178e4e917c4003b745827a46900486fe1ecc8b000f1fbb01a10f1cee`.
The same manifest, source, exit-code and oracle checks passed. Runs007 and008
match on the target `.olean`, the exact `oracle.log` bytes (SHA-256
`1aeb0c7f5efef1e4a9c6e2637c2f311ccbfcacff829808bbb243d9b4cdff9243`),
and `source-hashes.json` (SHA-256
`9000150ad797515946f35c6619be703e7dd1b0af329a33f6b66f4d8112e5d472`).
Both complete packages and their comparison are preserved under
[`reproducibility/paper47-20261029`](../reproducibility/paper47-20261029/).
This closes the two-fresh-clone requirement for the **focal target and oracle**;
it is not a repository-wide terminal audit.

Run007 executed 13:27:27–13:32:25 UTC; run008 executed 13:38:55–13:43:23 UTC,
both on 29 October 2026. Each released its own CPU/high-RAM runtime after
emitting a persistent inline evidence payload, and the reconnect control was
observed afterward. The elapsed run008 execution was 267.326 seconds; allocation
time is additional. Compute units were not measured and are not inferred from
elapsed time. No GPU or Windows compilation was used.

ZIP bytes and run reports include timestamps and timings; their hashes need not
match across runs. Compare the deterministic target artifact, source manifest,
and raw oracle output instead. Successful reproduction is not a new proof of
originality, a peer review, or an independent scientific assessment.

## Model assessments and review context

This supplement contains no scored model assessment of the PDF. Historical
ratings, if any, are not inherited by this artifact. The Colab runs are separate
execution sessions orchestrated in the same chat; that separation does not make
their interpretation independent human or model review. Exact-PDF review reports,
actual model identities, objections, and publication permissions must be recorded
before requesting a revised AIRR record. No new AIRR deposit is justified merely
by recovering reproduction logs.

## Scientific limits

See [the source-scope dictionary](FLAT-BLOCK-NOGO-SOURCE-SCOPE-20261029.md).
The unrestricted unit-spacing periodic flat form is not the gauge-restricted,
rescaled background operator in the primary sources. This result supplies no
Wilson Hessian coercivity theorem, physical spectral gap, continuum construction,
or new hRpoly terminal producer. PR29 remains 20/41 with TermSource=0.
