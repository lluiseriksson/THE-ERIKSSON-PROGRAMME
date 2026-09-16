# Step 8b.24 C6c.1 H1--H2d3 promotion and cold-seal checklist

Status: scratch only.  The 18 Lean blobs are statically staged but NOT CHECKED
by Lean.  This checklist neither authorizes promotion before the Step 8b.22
terminal verdict nor permits retirement of a PRE-VALIDATION marker.

## Promotion gate

1. Step 8b.22 must first have a terminal verdict and its downloaded artifact
   must pass `tmp/audit_step8b22_cold_evidence.py`.
2. All 92 files enumerated by `STEP8B24-ALL-PATHS.txt` (the complete Step
   8b.23 plus S1--C6b prefix), `STEP8B24-C6C1-PREFIX-PATHS.txt` (D1--D3),
   and `STEP8B24-C6C1-D4-PATHS.txt` (D4a--D4d) must exist as
   tracked public targets, contain no `PRE-VALIDATION:` marker, and every
   audit must already be imported by `YangMillsCore.lean`.  The promotion tool
   verifies the exact path-list hashes and refuses to proceed otherwise.
3. The tracked worktree and index must be clean at the exact intended base
   head.  Unrelated untracked files are preserved.
4. Run `tmp/promote_step8b24_c6c1_holder.py --expected-head <HEAD>` without
   `--write`.  Require literal `STEP8B24_C6C1_HOLDER_PROMOTION_DRY_RUN_OK`.
5. The dry run must regenerate and match manifest
   `5AABA4F160BC1FA0FB8BB58A81306275FB3A76B968F9F26411828E8AD482A6EC`:
   18 new files, 30 declarations, 30 axiom readouts and 19 topologically
   ordered internal import edges.
6. Only then repeat the same command with `--write`.  Inspect that the tracked
   delta contains exactly the 18 paths in
   `tmp/STEP8B24-C6C1-H1-H2B-PROMOTION-PATHS.txt`; do not edit
   `YangMillsCore.lean`, the vertical map or ledger in the source checkpoint.
7. Commit the 18 PRE-VALIDATION files as one source checkpoint and generate
   the Colab diagnostic runner and terminal workflow against its raw full SHA.
   The terminal workflow may replace only the already-dispatchable
   `validate-localized-carrier.yml` vehicle in a later commit.

## Cold evidence gate

The terminal run is one prepared cold checkout, `cold=true`, with no restored
`.lake/build`.  Require all 18 blob hashes, exact Lean 4.29.0-rc6 asset and
Mathlib `07642720480157414db592fa85b626dafb71355b`, 18 zero child exits, nine
literal final build sentinels, exactly 30 axiom blocks and literal
`FINAL_STATUS=PASS`.  Every axiom set must be a subset of
`{propext, Classical.choice, Quot.sound}` and neither `sorryAx` nor
`ofReduceBool` may occur.

Download both the raw outer ZIP and extracted artifact.  Run
`tmp/audit_step8b24_c6c1_holder_cold_evidence.py` and require literal
`STEP8B24_C6C1_HOLDER_COLD_EVIDENCE_OK`.  Preserve the source/workflow SHAs,
run/job URL, stage durations, job counts, all measured axiom sets, artifact id,
inner archive digest, raw ZIP digest and verified manifest/member counts.

## Exact seal scope on PASS

1. Remove exactly one `PRE-VALIDATION:` paragraph/comment from each of the 18
   H1--H2d3 source/audit files; no theorem statement or proof body changes.
2. Append exactly these nine imports, in queue order, after
   `BalabanCMP89Eq251LatticePhasePeriodicityAudit` in `YangMillsCore.lean`:

   ```text
   BalabanCMP89Eq249PhysicalFineHolderPhaseQuotientAudit
   BalabanCMP89Eq249ComplexStripHolderPhaseQuotientAudit
   BalabanCMP89Eq251AliasWeightExponentMonotonicityAudit
   BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotientAudit
   BalabanCMP89Eq249ComplexHolderRadialRedistributionAudit
   BalabanCMP89Eq249ComplexHolderAliasSummationAudit
   BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSumAudit
   BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranchAudit
   BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBoundAudit
   ```

3. Update `docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md` and append one new
   `docs/VERIFICATION-LEDGER.md` addendum with the measured evidence.  Do not
   preassign an addendum number; use the next number present at seal time.
4. State the delimitation literally: the seal proves H1, H2a, the physical
   local-pair specialization, radial redistribution, its one-weight alias
   summability, the noncentral phased Holder sum, the central zero-alias
   branch and their literal stabilized recombination.  It does not prove
   contour equality, identify signed L1 with the CMP89/source-owner metric,
   prove H3--H5, attain window 15, discharge a terminal field or inhabit
   `TermSource`.
5. Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
   compatible but unattained.

Any missing byte, axiom block, exit, sentinel, archive member or hash is
incomplete evidence.  Preserve the first real failure and do not retire marks,
move counters, rerun CI or infer a PASS from a visible prefix.
