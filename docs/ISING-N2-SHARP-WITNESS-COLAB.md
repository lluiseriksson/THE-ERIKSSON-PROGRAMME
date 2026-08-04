# Frozen Colab transcript: the sharp `N = 2`, `gamma = 0` witness

This is the manufacture record for Phase 0 only.  It reports a clean build of
the pre-registered witness and is not an external audit.  The independent
auditor should check out the raw proof SHA below; no result from task (42) was
read or used.

## Frozen source

- Raw proof SHA: `36a02972d0f6771acb2f9594b6306cc08db39faf`
- Base SHA: `1470b4e91b582b043a225957a112d94b9a6226c0`
- Base branch: `codex/spatial-ring-uniformity`
- Proof module: `YangMills/OS/SpatialSharpWitness.lean`
- Repository convention: physical `N = L + 1`; this witness fixes `L = 1`
  and `gamma = 0`.

The exact kernel and orbit folds frozen in that SHA are

```lean
n2TransferKernel beta sigma tau :=
  symWeighted (spatialWeightRing 0) beta sigma tau

n2EvenBlock beta i j :=
  n2TransferKernel beta (n2OrbitRep i) (n2OrbitRep j) +
    n2TransferKernel beta (n2OrbitRep i) (flipCfg (n2OrbitRep j))

n2OddBlock beta i j :=
  n2TransferKernel beta (n2OrbitRep i) (n2OrbitRep j) -
    n2TransferKernel beta (n2OrbitRep i) (flipCfg (n2OrbitRep j))
```

The norm is Mathlib's matrix L2 operator norm, selected by
`open scoped Matrix.Norms.L2Operator`.  The campaign constant specialized to
this witness is defined, rather than assumed, by

```lean
n2CandidateQ beta := Real.tanh beta * Real.exp (2 * (0 : Real))
```

## Exact headline and hypotheses

The named equality has the single mathematical hypothesis `hbeta : 0 < beta`:

```lean
theorem n2_sharp_norm_ratio {beta : ℝ} (hbeta : 0 < beta) :
    ‖n2OddBlock beta‖ / ‖n2EvenBlock beta‖ =
        Real.sinh (2 * beta) / (Real.cosh (2 * beta) + 1) ∧
    Real.sinh (2 * beta) / (Real.cosh (2 * beta) + 1) =
        n2CandidateQ beta ∧
    n2CandidateQ beta = Real.tanh beta
```

The sharpness and form counterexample are separately named:

```lean
theorem n2_no_strictly_smaller_constant {beta c : ℝ}
    (hbeta : 0 < beta) (hc : c < n2CandidateQ beta) :
    ¬ ‖n2OddBlock beta‖ / ‖n2EvenBlock beta‖ ≤ c

theorem n2_qEven_sub_odd_entry {beta : ℝ} (hbeta : 0 < beta) :
    (Real.tanh beta • n2EvenBlock beta - n2OddBlock beta) 0 0 =
      -2 * Real.tanh beta

theorem n2_form_domination_fails {beta : ℝ} (hbeta : 0 < beta) :
    (Real.tanh beta • n2EvenBlock beta - n2OddBlock beta) 0 0 < 0
```

No equality, norm formula, closed matrix form, or equivalent rewrite of the
conclusion is a hypothesis.  The closed blocks, their norms, and the
hyperbolic quotient are proved by explicit finite `2 x 2` algebra in the same
module.

## Reproduction environment and commands

- Colab Pro+ CPU runtime, signed in as `lluiseriksson@gmail.com`
- CPU: `Intel(R) Xeon(R) CPU @ 2.20GHz`
- GPU device: absent
- UTC start: `2026-08-03T16:46:22Z`
- UTC end: `2026-08-03T18:44:34Z`
- Runtime disconnected and deleted after transcript capture

A fresh clone was detached at the raw proof SHA.  Only the pinned dependency
package directory was copied from the earlier Colab clone; the project build
directory was fresh.

```text
git clone --filter=blob:none --branch codex/testigo-agudo-n2-q \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git \
  /content/eriksson-phase0-frozen
git checkout --detach 36a02972d0f6771acb2f9594b6306cc08db39faf
test "$(git rev-parse HEAD)" = \
  "36a02972d0f6771acb2f9594b6306cc08db39faf"
mkdir -p .lake
cp -a /content/eriksson-phase0/.lake/packages .lake/
lake exe cache get
lake build YangMills.OS.SpatialSharpWitness
lake build YangMillsCore
lake env lean oracle_check.lean
```

The command group ended with `COMMANDS_EXIT=0` and
`FROZEN_REPRO_EXIT=0`.  The module build completed successfully with 8172
jobs; the core build completed successfully with 8469 jobs.

## Original manufacture manifest

The manufacture transcript recorded the following four digests, but the raw
files themselves were not added to Git at `254687f52993aad70191c014bace1184a11487b5`.
That omission is the only provenance failure reported by the limited external
audit; the table is retained as historical metadata rather than presented as
an archived artifact.

| Log | Bytes | SHA-256 |
| --- | ---: | --- |
| `phase0_frozen_cache.log` | 139 | `18cfb29942326ace51032bafb8c557fb732db93edb34b6930fc372497a2503c1` |
| `phase0_frozen_module.log` | 2095 | `b84d58b9c33b65e3bdcba491f80e6e3167d7b5474147369782ec7fca998f3f14` |
| `phase0_frozen_core.log` | 106345 | `86e09b3fe3a14a06412931f7d464ca7b8040163fc8d87dcbfb100c3ecb30f465` |
| `phase0_frozen_oracle.log` | 346431 | `8dc4dfaa790d0d42155ac2ef9d1410a2dc2d47f78af512cc94b4f1a0f0a00188` |

## Forensic preservation rerun

On `2026-08-04T23:00:39Z`, a new disconnected notebook was prepared and then
run in a fresh Colab Pro+ CPU/high-RAM runtime with no GPU.  It cloned the same
branch, detached at the same raw proof SHA
`36a02972d0f6771acb2f9594b6306cc08db39faf`, verified a clean checkout, and
executed the same four commands.  All four exits were zero.  The module and
Core builds again completed with 8172 and 8469 jobs.

The complete byte streams are preserved under
`docs/audit-artifacts/pr62-colab-forensic/`:

| Log | Bytes | LF | CR | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| `phase0_frozen_cache.log` | 10173 | 49 | 88 | `36a184938168b7d019c5df0ea9cdedd29fc4dcd193ae5f29aa6e3d9f550a388a` |
| `phase0_frozen_module.log` | 2106 | 42 | 0 | `5544e5406d132928c735108062c3227435fda135697ffd66650594dd9e1f844f` |
| `phase0_frozen_core.log` | 106497 | 1643 | 0 | `67cc3646acf800c809d8e116d9c1c0c8652a7700b0487cef4d898d39d002817f` |
| `phase0_frozen_oracle.log` | 346431 | 5189 | 0 | `8dc4dfaa790d0d42155ac2ef9d1410a2dc2d47f78af512cc94b4f1a0f0a00188` |

The oracle log is byte-identical to the historical digest.  The cache log is
larger because this rerun acquired the toolchain and package cache in the new
runtime; build timing text also varies.  The Colab-generated `manifest.json`,
`transcript.txt`, `setup-transcript.txt`, and `SHA256SUMS` freeze the commands,
runtime, checkout, exits, bytes, line endings, and hashes.  The downloaded ZIP
was 44,156 bytes with SHA-256
`e11022dcee1a77637f6ab41aa03877c6905f6cc8158b47e33b4969bc1d0f6593`;
Windows verified that digest before extraction and then matched every entry in
`SHA256SUMS`.  Windows did not execute Lean, Lake, or the oracle.

## Focused oracle output

Each of the nine new declarations reported exactly the same standard axiom
set, `[propext, Classical.choice, Quot.sound]`:

```text
YangMills.OS.n2EvenBlock_closedForm
YangMills.OS.n2OddBlock_closedForm
YangMills.OS.n2EvenBlock_norm
YangMills.OS.n2OddBlock_norm
YangMills.OS.n2_scale_ratio_eq_tanh
YangMills.OS.n2_sharp_norm_ratio
YangMills.OS.n2_no_strictly_smaller_constant
YangMills.OS.n2_qEven_sub_odd_entry
YangMills.OS.n2_form_domination_fails
```

There are no project axioms and no `sorry` in the witness.  The frozen build
has one non-fatal style warning in the new module at line 190
(`unnecessarySeqFocus`); existing base warnings are also present.  This is
lint-only debt, not an open mathematical bridge.  No general uniform upper
bound, Clifford/Jordan--Wigner construction, or paper claim is made here.
