# Step 8b.24 C6c.8f1 local regularity witness promotion manifest

Status: PRE-VALIDATION / NOT PROMOTED / NOT COMPILER-VERIFIED.

This checkpoint is downstream of C6c.8f0a--f0b.  It must not touch the tracked
tree until the running Step8b22 cold terminal job has emitted a final verdict
and its evidence has been sealed or classified.  Current tracked HEAD is
`b05ef65af97a95752d1c929e30749d886d425d8d`.

## Exact scratch inputs

```text
14A29EC9FD6A0F75C22F3D38E2F8339AD80A8A2E8BCC732C4536087366A6A59E  tmp/BalabanCMP99Eq335PhysicalRegularityWitness.draft.lean
488A9B0B20F0F67B94A4A3EA1B21BB9A9325E9246512A46C0870E3ED69DBF4E4  tmp/BalabanCMP99Eq335PhysicalRegularityWitnessAudit.draft.lean
```

The exact six-file f0a/f0b/f1 overlay passes the lightweight delimiter,
import-order and `sorry`/`admit` gate.  The f1 audit queue contains 8 readouts.
These are text/mechanism checks only.

## Dependency order

```text
BalabanCMP99Eq335PhysicalForwardDerivative
BalabanCMP99Eq335PhysicalForwardDerivativeAudit
BalabanCMP99SourceRegularCube
BalabanCMP99SourceRegularCubeAudit
BalabanCMP99Eq335PhysicalRegularityWitness
BalabanCMP99Eq335PhysicalRegularityWitnessAudit
```

Diagnostics belong in a warm Colab checkout.  A seal requires a cold checkout
at the exact source SHA, exact toolchain/Mathlib pins, real exit codes and all
axiom readouts.  No exploratory GitHub Actions run is authorized.

## Semantic acceptance

- the gauge is a function only on the cube-site subtype;
- the exponential identity quantifies only over positive bonds whose source
  and target both lie in that same cube;
- there is no caller-supplied global gauge transform or global transformed
  background equality;
- the one-cochain extension outside the cube has no exported law and cannot
  reach the regional tower before the f2 locality theorem;
- the derivative bound uses the ordinary forward tensor from (3.35), not the
  covariant tensor (3.39) or a plaquette curl;
- `L`, `Mlarge`, `geometryFactor` and `eta` remain visibly distinct;
- counters remain `20/41`, `TermSource = 0`, window 15 unattained.
