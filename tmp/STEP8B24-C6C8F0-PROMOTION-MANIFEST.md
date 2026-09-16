# Step 8b.24 C6c.8f0 source dictionaries promotion manifest

Status: PRE-VALIDATION / NOT PROMOTED / NOT COMPILER-VERIFIED.

This checkpoint must not touch the tracked tree until the running Step8b22
cold terminal job has emitted a final verdict and its evidence has been sealed
or classified.  Current tracked HEAD is
`b05ef65af97a95752d1c929e30749d886d425d8d`.

## Exact scratch inputs

```text
65634E403FC0CF35029E063CB4EF35D494B653F0EF5EEC290BF80DD06CAADB6C  tmp/BalabanCMP99Eq335PhysicalForwardDerivative.draft.lean
72025C310AC02D756E7C9005FC006AAE42CA155D9859B7A36CEFA2310705FDF6  tmp/BalabanCMP99Eq335PhysicalForwardDerivativeAudit.draft.lean
99D178132F3869215529C8EC09C980BB2F06112B825A0860F4B442521790527B  tmp/BalabanCMP99SourceRegularCube.draft.lean
433DE67E650961C902F62B26B12A5EE6646C33B5DBC73C1E3FC42102B6514966  tmp/BalabanCMP99SourceRegularCubeAudit.draft.lean
```

The exact four-file overlay passes the lightweight delimiter/namespace and
`sorry`/`admit` gate in 118 ms.  Static audit queues contain 1 readout for
C6c.8f0a and 7 for C6c.8f0b.  These are text/mechanism checks only.

## Promotion mapping

Each `tmp/*.draft.lean` is copied byte-for-byte to the corresponding
`YangMills/RG/*.lean` path after removing only `.draft` from its filename.
PRE-VALIDATION stays visible until a sanctioned cold seal.  The diagnostic
commit adds neither root imports nor map/ledger claims.

## Stop-on-first-error order

```text
BalabanCMP99Eq335PhysicalForwardDerivative
BalabanCMP99Eq335PhysicalForwardDerivativeAudit
BalabanCMP99SourceRegularCube
BalabanCMP99SourceRegularCubeAudit
```

Diagnostics belong in a warm Colab checkout.  A seal requires a cold checkout
at the exact source SHA, exact toolchain/Mathlib pins, exit codes and all axiom
readouts.  No exploratory GitHub Actions run is authorized.

## Semantic acceptance

- the derivative is the ordinary `(mu,nu)` forward-difference tensor
  `nabla^eta A` printed in (3.35), with visible `eta^-1` and no background
  argument; it is not the covariant tensor of (3.39) or the plaquette curl;
- the regular cube carrier is generated from a periodic axis cube of
  `geometryFactor * M` scale sites and the existing `fineBlock` map;
- `geometryFactor >= 10` is the printed convention (never `<= 10`);
- the terminal adjacent stratum is the literal terminal `Omega` region and is
  proved empty from `global.final_empty`, not chosen by an external `if`;
- the two p. 396 stratum clauses and uniqueness of the scale index are visible;
- no arbitrary derivative, cube carrier, terminal stratum or `domainOf` is an
  input;
- counters remain `20/41`, `TermSource = 0`, window 15 unattained.
