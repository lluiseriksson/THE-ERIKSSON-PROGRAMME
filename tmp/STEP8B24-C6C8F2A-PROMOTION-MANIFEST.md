# Step 8b.24 C6c.8f2a Laplacian locality promotion manifest

Status: PRE-VALIDATION / NOT PROMOTED / NOT COMPILER-VERIFIED.

This is only the Laplacian sub-brick of f2.  It is downstream of f0a--f0b and
f1, and must not touch the tracked tree until the running Step8b22 cold job is
classified and sealed.  Current tracked HEAD is
`b05ef65af97a95752d1c929e30749d886d425d8d`.

## Exact scratch inputs

```text
C61E655058E81BF2E20C13F9426DB690C49E7C80EA3C2A3886156D629C0E3BCF  tmp/BalabanCMP99Eq335PhysicalRegularityLaplacianLocality.draft.lean
F503B6920E9C7DB5659916E22FBBA408BDE50979BC43C58CF432545DA14620C9  tmp/BalabanCMP99Eq335PhysicalRegularityLaplacianLocalityAudit.draft.lean
```

The exact pair passes the lightweight delimiter, import-order and
`sorry`/`admit` gate.  The audit queue contains 9 readouts.  This is no Lean
evidence.

## Semantic acceptance

- the read carrier is generated internally as all positive bonds with either
  endpoint in the active region;
- equality of `D_U` and then `D_U^* D_U` is derived from pointwise background
  agreement on that carrier;
- the cube-local gauge is extended by identity only as canonical derived data;
- no global gauge identity is assumed or claimed outside the cube;
- the collar-inside-cube premise is geometric and explicit;
- no regional derivative or Laplacian equality is a caller input;
- f2 remains open until source-contour and retained-average read carriers are
  also constructed;
- counters remain `20/41`, `TermSource = 0`, window 15 unattained.

Diagnostics belong in a warm Colab checkout.  A seal requires a cold checkout
at the exact source SHA, exact toolchain/Mathlib pins, real exit codes and all
axiom readouts.  No exploratory GitHub Actions run is authorized.
