# Step 8b.24 C6c.1 D1--D4d promotion and cold-seal checklist

Status: scratch only.  The 14 Lean blobs are statically staged but NOT CHECKED
by Lean.  This file is an ordering contract, not compiler evidence.

## Promotion gate

1. Step 8b.22 must have a terminal verdict and classified cold evidence.
2. All 78 targets in `STEP8B24-ALL-PATHS.txt` (Step 8b.23 A--F and Step
   8b.24 S1--C6b) must exist publicly, contain no `PRE-VALIDATION:` marker,
   and every one of their 39 audits must be imported by `YangMillsCore.lean`.
3. The tracked worktree and index must be clean at the explicit full base SHA.
4. Run `tmp/promote_step8b24_c6c1_derivative.py --expected-head <HEAD>`
   without `--write`.  Require literal
   `STEP8B24_C6C1_DERIVATIVE_PROMOTION_DRY_RUN_OK` and promoted manifest
   `7D82089113F6ADB6058C686ABA7B994B0C6B953C953BAE0555B07A6DE2792581`.
5. Only then repeat with `--write`.  The delta must be exactly the eight paths
   in `STEP8B24-C6C1-PREFIX-PATHS.txt` followed by the six paths in
   `STEP8B24-C6C1-D4-PATHS.txt`.  Do not edit `YangMillsCore.lean`, the
   vertical map or ledger in the source checkpoint.
6. Commit the 14 PRE-VALIDATION files as one source checkpoint.  Generate the
   diagnostic runner and terminal workflow only against that raw full SHA.

## Stop-on-first-error order

Run source then audit for each brick before continuing:

1. D1 `BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy`
2. D2a `BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift`
3. D2b `BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope`
4. D3 `BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformBound`
5. D4a--b `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift`
6. D4c `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization`
7. D4d `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative`

The audits must emit exactly the 33 declaration readouts fixed by
`audit_step8b24_c6c1_derivative_static.py`.  Every axiom set must be a subset
of `{propext, Classical.choice, Quot.sound}`; `sorryAx` and `ofReduceBool`
are forbidden.

## Cold seal

One prepared cold checkout (`cold=true`, no restored `.lake/build`) is enough
for this internal brick.  Require exact toolchain and Mathlib pins, exact 14
source blobs, all 14 child exits zero, all seven final build sentinels, all 33
axiom blocks and literal `FINAL_STATUS=PASS`.  Preserve the raw outer ZIP,
extracted evidence, archive and member hashes, run/job URL and stage timings.

Only after independent evidence validation may a seal remove exactly one
`PRE-VALIDATION:` marker from each of the 14 files, import the seven audits in
queue order into `YangMillsCore.lean`, and record the evidence in the vertical
map and ledger.

The delimitation is mandatory: D1--D4d supplies the ambient complex,
zero-mass left-derivative source-owner branch.  It does not prove the regional
left-derivative field, H1--H5, window-15 attainment, a terminal field or a
`TermSource` inhabitant.  Counters remain `20/41`, `TermSource = 0`.
