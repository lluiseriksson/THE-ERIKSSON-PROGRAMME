# C6d post-Eq360 boundary: regional precision to canonical Green

Status: static design plus PRE-VALIDATION scratch only.  No Lean/Lake or
axiom-oracle verdict is claimed here.  This boundary moves neither `20/41`
nor window 15 and constructs no `TermSource`.

## Measured carrier mismatch

The source-facing Eq. (3.35)/(3.60) precision is an endomorphism of

```text
ActiveGaugeZeroCochain Omega (SUNLieCoord Nc).
```

The reusable `cmp99RegionalDirichletGreen` and both Eq. (3.42) certificate
types instead start from an endomorphism of the full ambient zero-cochain
carrier and then apply `cmp99RegionalDirichletPrecision Omega`.

The existing CMP96 Green on
`cmp96SourceSeparatedRegionalCell P L K Q depth cell` cannot close this
boundary.  The selected Eq. (3.35) region is arbitrary source data constrained
by the printed source-region dictionary; it is not definitionally that
separated cell, and restriction of an inverse on a larger Dirichlet region is
not the inverse on a smaller one.

## Accepted adapter

For literal restriction `R`, zero extension `E`, and the regional physical
precision `K`, use the canonical ambient completion

```text
K_ambient = E K R + (I - E R).
```

The exterior identity is not a physical claim.  It is a fixed technical
completion whose irrelevance must be proved before any source estimate uses
it.  The proof chain is finite:

1. `ER` and `I-ER` give an exact Pythagorean coordinate splitting;
2. coercivity of `K` with constant `c` yields coercivity of `K_ambient` with
   constant `min c 1`;
3. `R K_ambient E = K` exactly;
4. the regional Dirichlet Green generated from `K_ambient` equals
   `covarianceOfIsCoerciveCLM K` by inverse uniqueness.

The PRE-VALIDATION implementation and audit are:

```text
tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletion.draft.lean
tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.draft.lean
```

Both lightweight text/import guards pass.  They remain scratch and may not be
cited until a compiler/audit gate passes and the exact files are promoted.

## What remains physical

This adapter does not manufacture any of the substantive source inputs.  A
source-facing consumer still has to:

1. construct the real physical Eq. (3.60) precision `K1` on `Omega`;
2. derive coercivity of `K1` from the baseline gap and the attained relative
   perturbation budget;
3. construct its canonical regional covariance through the adapter above;
4. prove the four Eq. (3.42) actions on that same covariance;
5. establish one depth-uniform `B0, delta0` pair and then attain
   `norm R' < 1` by the direct Eq. (3.89) route.

No ambient precision, Green, inverse equality, `B0`, `delta0`, coercivity
constant or contraction may be accepted as a renamed free input.

