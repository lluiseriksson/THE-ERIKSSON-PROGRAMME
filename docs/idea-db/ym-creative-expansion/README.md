# YM Creative Expansion Pack v4

**Post-integration mission-control edition.**

This pack assumes the creative expansion idea DB is already staged inside
`docs/idea-db/ym-creative-expansion/` and that Batch 003 proof-obligation cards
exist in the source DB.  v4 therefore focuses on **execution discipline**:
mission contracts, patch scoring, source-promotion state gates, and prompts that
force each agent to attack exactly one live hypothesis or blocker.

## Start here

1. Read `ops/AGENT_MISSION_CONTROL_v4.md`.
2. Pick one contract in `mission_contracts/README.md`.
3. Compile a prompt:

```bash
python scripts/compile_mission_prompt.py OC_001_eq231_source_subset_gapCarrier
```

4. After a candidate patch, fill `patch_intake/INTAKE_TEMPLATE.json` and score it:

```bash
python scripts/check_patch_contract.py \
  --contract mission_contracts/OC_001_eq231_source_subset_gapCarrier.json \
  --intake patch_intake/INTAKE_TEMPLATE.json
```

5. Validate the pack:

```bash
python scripts/validate_pack.py
python scripts/validate_mission_contracts.py
```

## Highest priority

`OC_001_eq231_source_subset_gapCarrier`.

Reason: it attacks one field of `CMP116Eq231BalabanPFamilySourcePackage`, and the
repository already has a Lean reducer from base-cube ownership to carrier
containment.  This is smaller and safer than trying to prove the full Eq. (2.31)
P-family membership iff in one pass.

## Guardrail

This pack is not source evidence, not a theorem, and not a route to import into
`YangMillsCore`.  It is a bounded planning artifact for agents.
