# Step 8b.24 C6c.1 H1--H2d3 validation queue (PRE-VALIDATION)

This queue is prepared but not authorized for execution until the in-flight
Step 8b.22 cold run has a terminal verdict and its evidence has been
classified, and the full Step-8b.23/S1--C6b/D1--D4 prefix has its own cold
seals.  It must run in Colab Pro+ CPU/high-RAM, never through local Windows
Lean/Lake.

## Promotion scope

The exact paths are listed in
`tmp/STEP8B24-C6C1-H1-H2B-PROMOTION-PATHS.txt`.  They are generated
deterministically from the scratch drafts by
`tmp/prepare_step8b24_c6c1_h1_h2b_overlay.py`.  The generator removes only the
scratch declaration suffix `_draft`; PRE-VALIDATION markings remain until a
cold seal.

Current static manifest:

```text
files          = 18
source modules = 9
audit modules  = 9
declarations   = 30
axiom readouts = 30
compiler state = NOT CHECKED
internal import edges = 19 (topologically ordered)
manifest SHA-256 = 5AABA4F160BC1FA0FB8BB58A81306275FB3A76B968F9F26411828E8AD482A6EC
```

## Prepared validation instrumentation

The future committed checkpoint is gated by the following scratch-only,
fail-closed instruments.  They have not generated or dispatched a workflow:

```text
generate_step8b24_c6c1_holder_validation_runner.py
  45E8B3C1B61C280222D2BA50F802546FFBB0FF76210942D0F06EB3EB821FDB85
generate_step8b24_c6c1_holder_terminal_workflow.py
  91E532D0C18245EED9484DBFEAE4A5CF686ECD9C5512158707D3C16B6887A976
audit_step8b24_c6c1_holder_cold_evidence.py
  30AFC954B1295C89E7F7A9BE7602A7659C1836BEA75D52112699E7E3D2FA68FE
test_step8b24_c6c1_holder_runner_generator.py
  A3AA905D2F872A02DDC021F62EA5AF9BA872D33D6700236FF1F8C958A3F531FF
test_step8b24_c6c1_holder_cold_evidence.py
  5E2E7EDA6BDD2A9334C62874DC6D66FC4593B51410DAF817983A151433A877D9
retrieve_step8b24_c6c1_holder_cold_evidence.ps1
  C8AA55845A110658EA35808D0F605FBA94343DFE3B6E79E93909B44FE0DE844E
promote_step8b24_c6c1_holder.py
  61FC3CEFE1165254B1A38CA89686E9DA821ABA1AA043B8A08227EE27F2C48B71
STEP8B24-C6C1-HOLDER-PROMOTION-SEAL-CHECKLIST.md
  357343380990D87610A73316223A2F3E159BF057A21A16B9CF7FD4FA00819A4B
```

The measured local synthetic gate passed in 0.189 s with a 25,247,744-byte
peak working set.  It compiled both generators and the embedded axiom parser,
accepted a complete synthetic package, and rejected both a tampered
`FINAL_STATUS` and a missing `PRE-VALIDATION` marker.  The retrieval script
also parsed successfully in 0.023 s.  These are instrumentation tests only;
they are not Lean evidence.

The exact regenerated 18-file overlay also passed the repository delimiter,
placeholder, import-prefix and exactly-one-`PRE-VALIDATION:` textual gates in
0.070 s with a 21,397,504-byte peak working set.  This caught and repaired the
missing colon in eight audit markers before any promotion or remote run.
An initial no-write promotion probe against exact head `b05ef65a...` completed
in 0.232 s with a 23,105,536-byte peak working set, but an adversarial review
showed that it did not encode the semantic prerequisite order.  That probe is
superseded and is not a valid promotion gate.  The repaired tool now requires
all 92 Step-8b.23/S1--C6b/D1--D4 prerequisite files to be publicly present,
sealed and imported by `YangMillsCore.lean`; it must reject the current head.
The repaired 92-file gate rejects exact head `b05ef65a...` at the first absent
prerequisite in 0.179 s with a 23,175,168-byte peak working set:

```text
HOLDER_PREREQUISITE_MISSING=YangMills/RG/BalabanCMP89CenteredBrillouinAffineSlice.lean
```

## Stop-on-first-error order

Run source then audit for each row before moving to the next row:

```text
1. lake build YangMills.RG.BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient
   lake env lean YangMills/RG/BalabanCMP89Eq249PhysicalFineHolderPhaseQuotientAudit.lean
   expected axiom blocks: 5

2. lake build YangMills.RG.BalabanCMP89Eq249ComplexStripHolderPhaseQuotient
   lake env lean YangMills/RG/BalabanCMP89Eq249ComplexStripHolderPhaseQuotientAudit.lean
   expected axiom blocks: 4

3. lake build YangMills.RG.BalabanCMP89Eq251AliasWeightExponentMonotonicity
   lake env lean YangMills/RG/BalabanCMP89Eq251AliasWeightExponentMonotonicityAudit.lean
   expected axiom blocks: 4

4. lake build YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient
   lake env lean YangMills/RG/BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotientAudit.lean
   expected axiom blocks: 2

5. lake build YangMills.RG.BalabanCMP89Eq249ComplexHolderRadialRedistribution
   lake env lean YangMills/RG/BalabanCMP89Eq249ComplexHolderRadialRedistributionAudit.lean
   expected axiom blocks: 3

6. lake build YangMills.RG.BalabanCMP89Eq249ComplexHolderAliasSummation
   lake env lean YangMills/RG/BalabanCMP89Eq249ComplexHolderAliasSummationAudit.lean
   expected axiom blocks: 2

7. lake build YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSum
   lake env lean YangMills/RG/BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSumAudit.lean
   expected axiom blocks: 2

8. lake build YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranch
   lake env lean YangMills/RG/BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranchAudit.lean
   expected axiom blocks: 5

9. lake build YangMills.RG.BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBound
   lake env lean YangMills/RG/BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBoundAudit.lean
   expected axiom blocks: 3
```

For diagnosis, resume at the first failed source/audit pair on the same exact
checkpoint; do not rerun certified prefixes.  A diagnostic pass may use a hot
Colab checkout.  PRE-VALIDATION removal requires a cold checkout with no
restoration of `.lake/build` and a package containing exact source SHA, path
hashes, child exit codes and all 30 axiom blocks.

## Acceptance and delimitation

Every readout must be a subset of
`[propext, Classical.choice, Quot.sound]`; any `sorryAx`, `ofReduceBool` or
unknown axiom is terminal failure.  A green queue proves only H1, global H2a,
the physical local-pair specialization, radial redistribution, uniform
summability of that one weight, the literal noncentral Holder alias sum on its
signed transport contour, the zero-alias central Holder branch, and their
literal recombination with the central fine-symbol multiplier and single
stabilized reciprocal. It still does not prove equality between real and
shifted contour integrals or identify signed `l1` with the source/owner metric.
It therefore does not move `20/41`, attain window 15 or inhabit `TermSource`.
